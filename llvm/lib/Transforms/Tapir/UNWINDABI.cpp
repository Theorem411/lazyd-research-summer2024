//===- UNWINDABI.cpp - Lower Tapir into UNWIND PRSC runtime system calls -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the UNWIND ABI to convert Tapir instructions to calls
// into the user-level-interrupts PRSC library.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Tapir/UNWINDABI.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/Tapir/Outline.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/EscapeEnumerator.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/TapirUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"


//TODO : Code refactoring
//TODO : Design document
//TODO : Need to manually add the function, can not inline it directly
using namespace llvm;

#define DEBUG_TYPE "unwindabi"

// Map from basic block and instruction in fast path to slow path
ValueToValueMapTy VMapUNWIND;
// Map from basic block and instruction in fast path to got stolen handler
ValueToValueMapTy VMapUNWINDGH; 
// Contain original fast path
SmallVector<BasicBlock*, 8> bbV2CloneUNWIND;
// JoinCntr
Value * joinCntrUNWIND;
// resume_parent_unwind
BasicBlock * resume_parent_unwind;

// unwind entry
BasicBlock * unwind_entry;

/// Helper methods for storing to and loading from struct fields.
static Value *GEP(IRBuilder<> &B, Value *Base, int field) {
  // return B.CreateStructGEP(cast<PointerType>(Base->getType()),
  //                          Base, field);
  return B.CreateConstInBoundsGEP2_32(nullptr, Base, 0, field);
}

static unsigned GetAlignment(const DataLayout &DL, StructType *STy, int field) {
  return DL.getPrefTypeAlignment(STy->getElementType(field));
}

static void StoreSTyField(IRBuilder<> &B, const DataLayout &DL, StructType *STy,
                          Value *Val, Value *Dst, int field,
                          bool isVolatile = false,
                          AtomicOrdering Ordering = AtomicOrdering::NotAtomic) {
  StoreInst *S = B.CreateAlignedStore(Val, GEP(B, Dst, field),
                                      GetAlignment(DL, STy, field), isVolatile);
  S->setOrdering(Ordering);
}

static Value *LoadSTyField(
    IRBuilder<> &B, const DataLayout &DL, StructType *STy, Value *Src,
    int field, bool isVolatile = false,
    AtomicOrdering Ordering = AtomicOrdering::NotAtomic) {
    LoadInst *L =  B.CreateAlignedLoad(GEP(B, Src, field),
                                     GetAlignment(DL, STy, field), isVolatile);
  L->setOrdering(Ordering);
  return L;
}

using TypeBuilderCache = std::map<LLVMContext *, StructType *>;

#define DEFAULT_GET_LIB_FUNC(name)                          \
  static Constant *Get_##name(Module& M) {                  \
    return M.getOrInsertFunction( #name,                    \
        TypeBuilder< name##_ty, false>::get(M.getContext()) \
      );                                                    \
  }

using addr_ty = void *;
using workcontext_ty = void * [8];

using push_ss_ty = void (void *);
DEFAULT_GET_LIB_FUNC(push_ss)

using pop_ss_ty = void (void );
DEFAULT_GET_LIB_FUNC(pop_ss)

using dec_ss_ty = void (void );
DEFAULT_GET_LIB_FUNC(dec_ss)

using DISULI_ty = void (void);
DEFAULT_GET_LIB_FUNC(DISULI)

using ENAULI_ty = void (void);
DEFAULT_GET_LIB_FUNC(ENAULI)

using exit_ty = void (int);
DEFAULT_GET_LIB_FUNC(exit);

using mysetjmp_callee_ty = int (void **);
DEFAULT_GET_LIB_FUNC(mysetjmp_callee);

using savecontext_ty = int (void);
DEFAULT_GET_LIB_FUNC(savecontext);

using resume2scheduler_ty = void (void );
DEFAULT_GET_LIB_FUNC(resume2scheduler)

using suspend2scheduler_ty = void (int * );
DEFAULT_GET_LIB_FUNC(suspend2scheduler)

using initworkers_env_ty = void (void );
DEFAULT_GET_LIB_FUNC(initworkers_env)

using deinitworkers_env_ty = void (void );
DEFAULT_GET_LIB_FUNC(deinitworkers_env)

using deinitperworkers_sync_ty = void(int, int);
DEFAULT_GET_LIB_FUNC(deinitperworkers_sync)

using initperworkers_sync_ty = void(int, int);
DEFAULT_GET_LIB_FUNC(initperworkers_sync)


#define UNWINDRTS_FUNC(name, CGF) Get__unwindrts_##name(CGF)


/// \brief Helper to find a function with the given name, creating it if it
/// doesn't already exist. If the function needed to be created then return
/// false, signifying that the caller needs to add the function body.
template <typename T>
static bool GetOrCreateFunction(const char *FnName, Module& M,
                                Function *&Fn,
                                Function::LinkageTypes Linkage =
                                Function::InternalLinkage,
                                bool DoesNotThrow = true) {
  LLVMContext &Ctx = M.getContext();

  Fn = M.getFunction(FnName);

  // if the function already exists then let the
  // caller know that it is complete
  if (Fn)
    return true;

  // Otherwise we have to create it
  FunctionType *FTy = TypeBuilder<T, false>::get(Ctx);
  Fn = Function::Create(FTy, Linkage, FnName, &M);

  // Set nounwind if it does not throw.
  if (DoesNotThrow)
    Fn->setDoesNotThrow();

  // and let the caller know that the function is incomplete
  // and the body still needs to be added
  return false;
}



static Function *Get__unwindrts_mysetjmp_callee(Module& M) {
    // Inline assembly to move the callee saved regist to rdi
    Function *Fn = nullptr;

    if (GetOrCreateFunction<mysetjmp_callee_ty>("mysetjmp_callee_llvm", M, Fn))
        return Fn;

    LLVMContext &Ctx = M.getContext();
    const DataLayout &DL = M.getDataLayout();

    BasicBlock *Entry                 = BasicBlock::Create(Ctx, "entry", Fn);
    BasicBlock *NormalExit            = BasicBlock::Create(Ctx, "normalExit", Fn);
    BasicBlock *ThiefExit             = BasicBlock::Create(Ctx, "thiefExit", Fn);

    Type *Int32Ty = TypeBuilder<int32_t, false>::get(Ctx);
    Value *ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);  
    Value *ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);  

    /*
      #define mysetjmp_callee_2(ctx)            \
      asm volatile("movq %[ARG], %%rdi\n"       \
      "movq %%rbp, 0(%%rdi)\n"                  \
      "movq %%rsp, 16(%%rdi)\n"                 \
      "movq %%rbx, 24(%%rdi)\n"                 \
      "movq %%r12, 32(%%rdi)\n"                 \
      "movq %%r13, 40(%%rdi)\n"                 \
      "movq %%r14, 48(%%rdi)\n"                 \
      "movq %%r15, 56(%%rdi)\n"                 \
      ::[ARG] "r" (ctx):"rdi");                 \

    */
    
    Function::arg_iterator args = Fn->arg_begin();
    Value *argsCtx = &*args;

    using AsmTypCallee = void ( void** );
    FunctionType *FAsmTypCallee = TypeBuilder<AsmTypCallee, false>::get(Ctx);

    Value *Asm = InlineAsm::get(FAsmTypCallee, "movq $0, %rdi\nmovq %rbp, 0(%rdi)\nmovq %rsp, 16(%rdi)\nmovq %rbx, 24(%rdi)\nmovq %r12, 32(%rdi)\nmovq %r13, 40(%rdi)\nmovq %r14, 48(%rdi)\nmovq %r15, 56(%rdi)\n", "r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    IRBuilder<> B(Entry);
    
    Value * res = B.CreateCall(Asm, argsCtx);

    //Value * loadCtx =  B.CreateLoad(argsCtx);
    //loadCtx->dump();
    Value * loadIdx =  B.CreateConstGEP1_32(argsCtx, 1);
   
    B.CreateStore( BlockAddress::get(ThiefExit), loadIdx);

#if 0    
    Type *Int8Ty = TypeBuilder<int8_t, false>::get(Ctx);
    AllocaInst * aI = B.CreateAlloca(Int8Ty);
    B.CreateStore(ConstantInt::get(Int8Ty, 1, /*isSigned=*/false), aI);
    Value * oneInt8 = ConstantInt::get(Int8Ty, 1, false);
    Value * loadVal = B.CreateLoad(aI);
    Value * isEqOne = B.CreateICmpEQ(loadVal, oneInt8);
#endif
    
    Function * potentialJump = Intrinsic::getDeclaration(&M, Intrinsic::x86_uli_potential_jump);
    B.CreateCall(potentialJump, {BlockAddress::get(ThiefExit)});
    B.CreateBr(NormalExit);
    {
        B.SetInsertPoint(NormalExit);
        B.CreateRet(ZERO);
    }
    {        
        B.SetInsertPoint(ThiefExit);
        // Force to create the return label. 
        B.CreateFence(AtomicOrdering::SequentiallyConsistent);
        B.CreateRet(ONE);
    }

    return Fn;
}

/// \brief Get or create a LLVM function for savecontext.
/// It is equivalent to the following C code
///
/// int savecontext() {
///    unsigned ptr = (seed_ptr - seed_bp[threadId]);
///    void ** ctx  = (void**) workctx_arr[threadId][ptr]; // Not done
///
///    if(!mysetjmp_callee(ctx)) {
///        void ** addrRA = ((void**)*(seed_ptr+1)); // Not done
///        //*addrRA = popworkRetAddr;
///
///        if(seed_ptr == seed_bp[threadId]){
///            exit(0);
///        }
///       
///        TODO : Check if everything is expected
///        addrRA = ((void**)*(seed_ptr-1)); // Check
///        if ( addrRA && *(addrRA) != unwindRetAddr){   // Check
///            exit(0);
///        } else {
///            seed_ptr--; // Check
///            return 0;
///        }
///    } 
///    return 1;    
///
/// }
static Function *Get__unwindrts_savecontext(Module& M) {
  Function *Fn = nullptr;

  if (GetOrCreateFunction<savecontext_ty>("savecontext_llvm", M, Fn))
    return Fn;

  LLVMContext &Ctx = M.getContext();
  const DataLayout &DL = M.getDataLayout();

  BasicBlock *Entry                 = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *ThiefEntry            = BasicBlock::Create(Ctx, "thiefEntry", Fn);
  BasicBlock *AttemptUnwinding      = BasicBlock::Create(Ctx, "attemptUnwinding", Fn);
  BasicBlock *AttemptUnwindCont     = BasicBlock::Create(Ctx, "attemptUnwindCont", Fn);
  BasicBlock *ReachTopStack         = BasicBlock::Create(Ctx, "reachTopStack", Fn);
  BasicBlock *ReachAlreadyConverted = BasicBlock::Create(Ctx, "reachAlreadyConverted", Fn);
  BasicBlock *AddrNull              = BasicBlock::Create(Ctx, "addrNull", Fn);
  BasicBlock *KeepUnwinding         = BasicBlock::Create(Ctx, "keepUnwinding", Fn);     
  BasicBlock *CheckRA               = BasicBlock::Create(Ctx, "checkRA", Fn);     

  Type *Int32Ty = TypeBuilder<int32_t, false>::get(Ctx);
  Value *ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
  Value *EIGHT = ConstantInt::get(Int32Ty, 8, /*isSigned=*/false);  
  Value *ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);  
  
  // Create the TLS needed, seed_ptr
  // Create global structure (or the single link)            
  M.getOrInsertGlobal("seed_ptr", TypeBuilder<addr_ty*, false>::get(Ctx) );
  GlobalVariable * gSeed_ptr = M.getNamedGlobal("seed_ptr");
  gSeed_ptr->setLinkage(GlobalValue::ExternalLinkage);
  gSeed_ptr->setThreadLocal(true);

  M.getOrInsertGlobal("seed_sp", TypeBuilder<addr_ty*, false>::get(Ctx) );
  GlobalVariable * gSeed_sp = M.getNamedGlobal("seed_sp");
  gSeed_sp->setLinkage(GlobalValue::ExternalLinkage);
  gSeed_sp->setThreadLocal(true);
  
  // Thread ID
  M.getOrInsertGlobal("threadId", TypeBuilder<int, false>::get(Ctx) );
  GlobalVariable * gThreadId = M.getNamedGlobal("threadId");
  gThreadId->setLinkage(GlobalValue::ExternalLinkage);
  gThreadId->setThreadLocal(true);

  // Create the global variable needed, seed_bp[]
  M.getOrInsertGlobal("seed_bp",  TypeBuilder<addr_ty**, false>::get(Ctx)  );
  GlobalVariable * gSeed_bp = M.getNamedGlobal("seed_bp");
  gSeed_bp->setLinkage(GlobalValue::ExternalLinkage);

  M.getOrInsertGlobal("unwindRetAddr", TypeBuilder<addr_ty, false>::get(Ctx)  );
  GlobalVariable * gUnwindRetAddr = M.getNamedGlobal("unwindRetAddr");
  gUnwindRetAddr->setLinkage(GlobalValue::ExternalLinkage);
  gUnwindRetAddr->setThreadLocal(true);

  // Work Ctx arr
  M.getOrInsertGlobal("workctx_arr", TypeBuilder<workcontext_ty,false>::get(Ctx)->getPointerTo()->getPointerTo() );
  GlobalVariable * gWorkContext = M.getNamedGlobal("workctx_arr");
  gWorkContext->setLinkage(GlobalValue::ExternalLinkage);

  Constant * EXIT = Get_exit(M);

  IRBuilder<> B(Entry);
  {
      
      ///    unsigned ptr = (seed_ptr - seed_bp[threadId]);      
      Value * gSeed_bpVal = B.CreateLoad(gSeed_bp);    
      Value * gThreadIdVal = B.CreateLoad(gThreadId);
      Value * gSeed_ptrVal = B.CreateLoad(gSeed_ptr);
      

      Value * bp_location = B.CreateInBoundsGEP(gSeed_bpVal, gThreadIdVal); 
      bp_location->dump();

      Value * gSeed_bpEntry = B.CreateLoad(bp_location);    
      gSeed_bpEntry->dump();
      
      // Convert void_ptr_ptr to integer
      Value * cvrt2 = B.CreateCast(Instruction::PtrToInt, gSeed_bpEntry, Type::getInt32Ty(Ctx));
      Value * cvrt1 = B.CreateCast(Instruction::PtrToInt, gSeed_ptrVal, Type::getInt32Ty(Ctx));
    
      Value * seedOffset = B.CreateSub(cvrt1, cvrt2);    
      seedOffset->dump();

      ///    void ** ctx  = (void**) workctx_arr[threadId][ptr]; 
      Value * workCtxLoad = B.CreateLoad( gWorkContext);
      Value * idx2 = B.CreateInBoundsGEP(workCtxLoad, gThreadIdVal);
      Value * loadIdx2 = B.CreateLoad( idx2 );
      Value * idx1 = B.CreateInBoundsGEP(loadIdx2, seedOffset);
      Value * loadIdx1bitcast = B.CreateConstInBoundsGEP2_64( idx1, 0, 0);
      Constant* MYSETJMP_CALLEE = Get__unwindrts_mysetjmp_callee(M);           
      
      // seed_ptr--;
      // %13 = load i8**, i8*** @seed_sp, align 8
      // %incdec.ptr = getelementptr inbounds i8*, i8** %13, i32 -1
      // store i8** %incdec.ptr, i8*** @seed_sp, align 8                    
      Value * addPtr = B. CreateConstGEP1_32(gSeed_ptrVal,  -1);
      B.CreateStore(addPtr, gSeed_ptr);              
      

      Value * result = B.CreateCall(MYSETJMP_CALLEE, {loadIdx1bitcast});  
      dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);

      Value * isEqOne = B.CreateICmpEQ(result, ONE);
      B.CreateCondBr(isEqOne, ThiefEntry, AttemptUnwinding);

      //Thief 
      {
          B.SetInsertPoint(ThiefEntry);
          B.CreateRet(ONE);
      }


      // Keep unwinding
      {
          B.SetInsertPoint(AttemptUnwinding);
          // Create another basic block that exits
      
          Value * isEqOne = B.CreateICmpEQ(seedOffset, EIGHT);
          B.CreateCondBr(isEqOne, ReachTopStack, AttemptUnwindCont);
          
          // Reach top of stack
          {
              B.SetInsertPoint(ReachTopStack);
              B.CreateCall(EXIT, {ZERO});
              B.CreateBr(ThiefEntry);
              //B.CreateUnreachable();
          }
          
          // Attempt Keep unwinding
          {
              B.SetInsertPoint( AttemptUnwindCont);            

              
              //addrRA = ((void**)*(seed_ptr-1)); // This one 
              
              //%4 = load i8**, i8*** @seed_ptr, align 8
              //%add.ptr = getelementptr inbounds i8*, i8** %4, i64 -1
              //%5 = load i8*, i8** %add.ptr, align 8
              //%6 = bitcast i8* %5 to i8**
              //store i8** %6, i8*** %addrRA, align 8


              Value * addPtrVal = B.CreateLoad(addPtr);
              Value * addBitCastVal = B.CreateBitCast(addPtrVal, addPtrVal->getType()->getPointerTo());

              Value * pred1 = B.CreateICmpEQ( addBitCastVal, 
                                              ConstantPointerNull::get(dyn_cast<PointerType>(addBitCastVal->getType())));
              
              // If addr == NULL              
              B.CreateCondBr(pred1, AddrNull, CheckRA);

              B.SetInsertPoint(AddrNull);
              B.CreateCall(EXIT, {ZERO});
              B.CreateBr( ThiefEntry);
              
              B.SetInsertPoint(CheckRA);
              Value * loadAddr1  = B.CreateLoad(addBitCastVal);
              Value * loadUnwindAddr1 = B.CreateLoad(gUnwindRetAddr);              
              Value * pred2 = B.CreateICmpEQ(loadAddr1, loadUnwindAddr1);                           

              B.CreateCondBr(pred2, KeepUnwinding, ReachAlreadyConverted);
              {
                  B.SetInsertPoint( ReachAlreadyConverted );
                  B.CreateCall(EXIT, {ZERO});
                  B.CreateBr(ThiefEntry);
              }

              {
                  B.SetInsertPoint( KeepUnwinding );           
                  B.CreateRet(ZERO);
              }
          }

          //B.CreateCall(EXIT, {ZERO});
          //B.CreateUnreachable();
          //B.CreateRet(ZERO);
      }
  }
  
  //Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}


Value *UNWINDABI::lowerGrainsizeCall(CallInst *GrainsizeCall) {
  assert(false);
  return nullptr;
}

void UNWINDABI::createSync(SyncInst &SI, ValueToValueMapTy &DetachCtxToStackFrame) {    
    SyncInst* syncClone = dyn_cast<SyncInst>(VMapUNWIND[&SI]);
    
    BasicBlock * curBB = SI.getParent();
    Function * F = curBB->getParent();
    Module * M = F->getParent();
    LLVMContext& C = M->getContext();
    
    BasicBlock * bb = nullptr;
    Instruction * term = nullptr;
    
    // Build type
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);

    // Common Used Function
    Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
    Function * getSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);
    Function * setupRBPfromRSPinRBP = Intrinsic::getDeclaration(M, Intrinsic::x86_setup_rbp_from_sp_in_rbp);
    Constant * PUSH_SS = Get_push_ss(*M);
    Constant * POP_SS = Get_pop_ss(*M);
    Constant * resume2scheduler = Get_resume2scheduler(*M);
    Value * OneByte = ConstantInt::get(Int64Ty, 8, /*isSigned=*/false);
    Value * TwoByte = ConstantInt::get(Int64Ty, 16, /*isSigned=*/false);


    // Fast Path
    // ----------------------------------------------
    {
        BasicBlock * succ = SI.getSuccessor(0);
    }

    // Slow Path
    // ---------------------------------------------
    {
        // clone of syncBB will become the steal request handler        
        SmallVector<BasicBlock*, 8> bbList;
        DenseMap<BasicBlock *, bool> haveVisited;
        
        BasicBlock * syncBB = syncClone->getParent();
        Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  
        Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  

        IRBuilder<> slowBuilder( syncBB->getTerminator()  );
    }

    return;
}


Function *UNWINDABI::createDetach(DetachInst &Detach,
                        ValueToValueMapTy &DetachCtxToStackFrame,
                        DominatorTree &DT, AssumptionCache &AC) {
    
    BasicBlock * curBB = Detach.getParent();
    Function * F = curBB->getParent();
    Module * M = F->getParent();
    LLVMContext& C = M->getContext();
    
    BasicBlock * bb = nullptr;
    Instruction * term = nullptr;
    
    // Build type
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);

    // Common Used Function
    Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
    Function * getSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);
    Function * setupRBPfromRSPinRBP = Intrinsic::getDeclaration(M, Intrinsic::x86_setup_rbp_from_sp_in_rbp);
    

    Constant * DISULI = Get_DISULI(*M);
    Constant * ENAULI = Get_ENAULI(*M);
    

    Constant * PUSH_SS = Get_push_ss(*M);
    Constant * POP_SS = Get_pop_ss(*M);
    Constant * suspend2scheduler = Get_suspend2scheduler(*M);
    Constant * resume2scheduler = Get_resume2scheduler(*M);
    Value * OneByte = ConstantInt::get(Int64Ty, 8, /*isSigned=*/false);


    // GotStolen Handler
    // ----------------------------------------------
    {
        // Clone detach Block 
        // Create label after the call inst. This will be the got stolen handler
        // -------------------------------------------------------------------------
        DebugInfoFinder DIFinder;      
        DISubprogram *SP = F->getSubprogram();
        if (SP) {
            //assert(!MustCloneSP || ModuleLevelChanges);
            // Add mappings for some DebugInfo nodes that we don't want duplicated
            // even if they're distinct.
            auto &MD = VMapUNWINDGH.MD();
            MD[SP->getUnit()].reset(SP->getUnit());
            MD[SP->getType()].reset(SP->getType());
            MD[SP->getFile()].reset(SP->getFile());  
            MD[SP].reset(SP); 
        }        

    
        // Perform the actual cloning
        BasicBlock * detachBB = Detach.getDetached(); 
        BasicBlock * stolenhandler      = CloneBasicBlock(detachBB, VMapUNWINDGH, ".gotstolen", F, nullptr, &DIFinder);
        VMapUNWINDGH[detachBB]      = stolenhandler;        
     
        // --------------------------------------------------------------
        // Remap the cloned instruction
        for (Instruction &II : *stolenhandler) {
            RemapInstruction(&II, VMapUNWINDGH, RF_IgnoreMissingLocals, nullptr, nullptr);
        }

        // Add potential jump from detachBB to got stolen handler
        // Add potential jump after "spawn to fib" to avoid merging the gotstolen handler and the detachBlock
        IRBuilder<> builder(detachBB->getTerminator()); 
        builder.CreateCall(potentialJump, {BlockAddress::get( stolenhandler )});
        
        builder.SetInsertPoint(stolenhandler->getTerminator());
        Value * pJoinCntr = builder.CreateBitCast(joinCntrUNWIND, IntegerType::getInt32Ty(C)->getPointerTo());
        builder.CreateCall(suspend2scheduler, pJoinCntr);
        

        Instruction * iterm = stolenhandler->getTerminator();
        BranchInst *resumeBr = BranchInst::Create(resume_parent_unwind);
        ReplaceInstWithInst(iterm, resumeBr);

        // Split basic block here. Used as hack to reload join counter in -0O
        stolenhandler->splitBasicBlock(stolenhandler->getTerminator()->getPrevNode());


        for( Instruction &II : *detachBB){
          if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->hasFnAttribute(Attribute::Forkable)){                    
            // Associate callsite instruction with got-stolen handler
            M->CallStealMap[&II].stolenHandler = stolenhandler;          
            break;
          }
        } 

        M->StolenHandlerExists[stolenhandler] = true;

    }

    // Create the Fast Path
    //-------------------------------------------------------------------
    {
        // Add the prologue at beginning of the deattach block

        SmallVector<BasicBlock*, 8> bbList;
        DenseMap<BasicBlock *, bool> haveVisited;

        BasicBlock * detachBB = Detach.getDetached();        
        BasicBlock * continueBB = Detach.getContinue();
        Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  
        Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  

        BasicBlock   * startOfStealHandler = NULL;
        ReattachInst * prevReattachInst = NULL;

        IRBuilder<> fastBuilder(detachBB->getFirstNonPHIOrDbgOrLifetime()); 
        
        // Build the Fast Path Prologue
        // push_ss((void*) (builtin_sp() - 8) );
        Value * SPVal = fastBuilder.CreateCall(getSP);
        Value * SPValInt = fastBuilder.CreateCast(Instruction::PtrToInt, SPVal, IntegerType::getInt64Ty(C));
        Value * ppRA  = fastBuilder.CreateSub(SPValInt, OneByte);
        ppRA = fastBuilder.CreateCast(Instruction::IntToPtr, ppRA, IntegerType::getInt8Ty(C)->getPointerTo());
        Value * result = fastBuilder.CreateCall(PUSH_SS, {ppRA});

        /*
        llvm::InlineFunctionInfo ifi;
        if(llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true)){
            errs() << "Able to inline push_ss function\n";
        } else {
            errs() << "UnableAble to inline push_ss function\n";
        }
        */


        // Book Keeping
        startOfStealHandler = continueBB;
        for( Instruction &II : *detachBB){
            if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->hasFnAttribute(Attribute::Forkable) ){
                BasicBlock * stealhandler = dyn_cast<BasicBlock>(VMapUNWIND[startOfStealHandler]);                    
                // Associate callsite instruction with steal handler
                M->CallStealMap[&II].stealHandler = stealhandler;
                // Associate callsite instruction with unwind handler
                M->CallStealMap[&II].unwindHandler = unwind_entry;
                // Indicate the steal hander basic block needs a label
                M->StealHandlerExists[stealhandler] = true;                    

                break;
            }
        }


        bbList.clear();
        haveVisited.clear();
        // Look for the reattach inst
        // Add an epilogue just before it
        bbList.push_back(detachBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator() ))  ){
                // Don't push anynore if we encountered reattach instruction
                fastBuilder.SetInsertPoint(bb->getTerminator());
                fastBuilder.CreateCall(POP_SS);
 

            } else {
                for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
                    bbList.push_back(*SI);
                }
            }
        }



    }
    // Create the Slow path
    //-------------------------------------------------------------------
    
    // Slow path
    DetachInst* detachClone = dyn_cast<DetachInst>(VMapUNWIND[&Detach]);
    assert(detachClone);
    {
        // clone of DetachBB will become the steal request handler
        SmallVector<BasicBlock*, 8> bbList;
        DenseMap<BasicBlock *, bool> haveVisited;

   
        BasicBlock * detachBB = detachClone->getDetached();        
        BasicBlock * continueBB = detachClone->getContinue();
        Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  
        Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  

        BasicBlock   * startOfStealHandler= NULL;
        ReattachInst * prevReattachInst = NULL;

        IRBuilder<> slowBuilder(continueBB->getFirstNonPHIOrDbgOrLifetime()); 
        startOfStealHandler = continueBB;        
        //__builtin_setup_rbp_from_sp_in_rbp();
        slowBuilder.CreateCall(setupRBPfromRSPinRBP);
        
        bbList.clear();
        haveVisited.clear();
        // Look for the reattach inst
        // Add an epilogue just before it
        bbList.push_back(continueBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator())) || ( term = dyn_cast<SyncInst>( bb->getTerminator())) ){
                // Don't push anynore if we encountered reattach instruction
                slowBuilder.SetInsertPoint(bb->getTerminator());

                using AsmTypI = void ( int* );
                FunctionType *FAsmTypI = TypeBuilder<AsmTypI, false>::get(C);
                Value *Asm = InlineAsm::get(FAsmTypI, "movq $0, 0(%rsp)\0A\09", "r,~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
                // Store the result to storeInst
                Value * pJoinCntr = slowBuilder.CreateBitCast(joinCntrUNWIND, IntegerType::getInt32Ty(C)->getPointerTo());
                slowBuilder.CreateCall(Asm, pJoinCntr);

                using AsmTypV = void ( void* );
                FunctionType *FAsmTypV = TypeBuilder<AsmTypV, false>::get(C);
                Asm = InlineAsm::get(FAsmTypV, "movq $0, 16(%rsp)\0A\09", "r,~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
                slowBuilder.CreateCall(Asm, BlockAddress::get( resume_parent_unwind ));        
                slowBuilder.CreateCall(resume2scheduler);


            } else {
                for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
                    bbList.push_back(*SI);
                }
            }
        }        
    }
    //-------------------------------------------------------------------

    return NULL;
}


void UNWINDABI::preProcessFunction(Function &F) {

  Module *M = F.getParent();
  LLVMContext& C = M->getContext();
  const DataLayout &DL = M->getDataLayout();
  Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);
  Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);

  Value * ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);
  Value * ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);

  Constant * INITWORKERS_ENV = Get_initworkers_env(*M);
  Constant * DEINITWORKERS_ENV = Get_deinitworkers_env(*M);
  Constant * INITPERWORKERS_SYNC = Get_initperworkers_sync(*M);
  Constant * DEINITPERWORKERS_SYNC = Get_deinitperworkers_sync(*M);

  Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
  IRBuilder<> builder( C );


  // Add Thread initialization and deinitialization on the main function
  // TODO : Make this optional
  if ( F.getName() == "main") {
    
    // Initialize the PRSC at the beginning of main
    IRBuilder<> B(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

    /*

      // This tries to get debug info from the instruction before which a new
      // instruction will be inserted, and if there's no debug info in that
      // instruction, tries to get the info instead from the previous instruction (if
      // any). If none of these has debug info and a DISubprogram is provided, it
      // creates a dummy debug info with the first line of the function, because IR
      // verifier requires all inlinable callsites should have debug info when both a
      // caller and callee have DISubprogram. If none of these conditions are met,
      // returns empty info.
      static DebugLoc getOrCreateDebugLoc(const Instruction *InsertBefore,
      DISubprogram *SP) {
         assert(InsertBefore);
         if (InsertBefore->getDebugLoc())
           return InsertBefore->getDebugLoc();
         const Instruction *Prev = InsertBefore->getPrevNode();
         if (Prev && Prev->getDebugLoc())
           return Prev->getDebugLoc();
         if (SP)
           return DILocation::get(SP->getContext(), SP->getLine(), 1, SP);
         return DebugLoc();
      }

     */

    // Works!
    DISubprogram *SP = F.getSubprogram();
    DebugLoc DL = DILocation::get(SP->getContext(), SP->getLine(), 1, SP);
    B.SetCurrentDebugLocation(DL);
    B.CreateCall(INITWORKERS_ENV);
    B.CreateCall(INITPERWORKERS_SYNC,  {ZERO, ONE});   


    for (auto &BB : F){
      Instruction * termInst = BB.getTerminator();
      if(isa<ReturnInst>(termInst)){
          B.SetInsertPoint(termInst);
          B.CreateCall(DEINITPERWORKERS_SYNC, { ZERO, ONE});
          B.CreateCall(DEINITWORKERS_ENV);
      }
    }   

    return;
  } 

  
  // Clone the function, create the slow path
  // Clone the basic block
  // -------------------------------------------------------------------------
  DebugInfoFinder DIFinder;      
  DISubprogram *SP = F.getSubprogram();
  if (SP) {
      //assert(!MustCloneSP || ModuleLevelChanges);
      // Add mappings for some DebugInfo nodes that we don't want duplicated
      // even if they're distinct.
      auto &MD = VMapUNWIND.MD();
      MD[SP->getUnit()].reset(SP->getUnit());
      MD[SP->getType()].reset(SP->getType());
      MD[SP->getFile()].reset(SP->getFile());  
      MD[SP].reset(SP); 
  }

  // Delete the alloca in the cloned entry so that it is not used during remap
  SmallVector<Instruction *,2> delInstrs;
  
  // Collect the basic block to clone
  for( auto &BB : F){
      bbV2CloneUNWIND.push_back(&BB);
  }
  
  BasicBlock * entryBB =  dyn_cast<BasicBlock>( &F.getEntryBlock());
  // Perform the actual cloning
  for (auto pBB : bbV2CloneUNWIND){
      BasicBlock *bbC = CloneBasicBlock(pBB, VMapUNWIND, ".clone", &F, nullptr, &DIFinder);
      VMapUNWIND[pBB] = bbC;        
     
      if(pBB == entryBB){
          builder.SetInsertPoint(entryBB->getTerminator());
          builder.CreateCall(potentialJump, {BlockAddress::get(bbC)});
      }

  }
   
  // --------------------------------------------------------------
  // Remap the cloned instruction
  for (auto pBB : bbV2CloneUNWIND){
      BasicBlock* bbC = dyn_cast<BasicBlock>(VMapUNWIND[pBB]);
      for (Instruction &II : *bbC) {
          RemapInstruction(&II, VMapUNWIND,
                           RF_IgnoreMissingLocals,
                           nullptr, nullptr);
      }
  }
  
  // --------------------------------------------------------------
  // Fixed clone inst. 
  // In slow path
  // 1. Looked for alloca inst.
  // 2. Replace all uses with the original instruction
  // 3. Delete the alloca inst. 
  for (auto pBB : bbV2CloneUNWIND){
      for (Instruction &II : *pBB) {
          if(isa<AllocaInst>(&II)){
              Instruction * iclone = dyn_cast<Instruction>(VMapUNWIND[&II]);
              iclone->replaceAllUsesWith(&II);
              delInstrs.push_back(iclone);
          }
      }
  }
  for(auto II : delInstrs){
      II->eraseFromParent();
  }


  // -------------------------------------------------
  // Add forkable attribute
  for (auto pBB : bbV2CloneUNWIND){
      if (DetachInst * DI = dyn_cast<DetachInst>(pBB->getTerminator())){          
          BasicBlock * detachBlock = dyn_cast<DetachInst>(DI)->getDetached();
          for( Instruction &II : *detachBlock ) {
              if( isa<CallInst>(&II) ) {
                dyn_cast<CallInst>(&II)->getCalledFunction()->addFnAttr(Attribute::Forkable);                
            }
          }
      }
  }

  // -------------------------------------------------------------
  // Create the resume path
  for (auto pBB : bbV2CloneUNWIND){
      if( SyncInst *SI = dyn_cast<SyncInst>(pBB->getTerminator()) ){
          Function *SetupRBPfromRSP = Intrinsic::getDeclaration(M, Intrinsic::x86_setup_rbp_from_rsp);
          Constant * DEC_SS = Get_dec_ss(*M);
          // Resume Parent path
          {
              resume_parent_unwind = BasicBlock::Create(C, "resume_parent_unwind", &F);
              IRBuilder <> B(resume_parent_unwind);
              
              // Set debug location (hack)
              DISubprogram *SP = F.getSubprogram();
              DebugLoc DL = DILocation::get(SP->getContext(), SP->getLine(), 1, SP);
              B.SetCurrentDebugLocation(DL);
    

              B.CreateCall(SetupRBPfromRSP);

              CallInst* callInst = B.CreateCall(DEC_SS);
              B.SetCurrentDebugLocation(B.getCurrentDebugLocation());
              B.SetInstDebugLocation(callInst);

              B.CreateBr(SI->getSuccessor(0));
              
              // Add a potential jump from entry to resume_parent_unwind block
              builder.SetInsertPoint(entryBB->getTerminator());
              builder.CreateCall(potentialJump, {BlockAddress::get(resume_parent_unwind)});
          }
      }
  }

  // -------------------------------------------------------------
  // Create the unwind path
  {
      unwind_entry = BasicBlock::Create(C, "unwind_path", &F);
      BasicBlock * unwind_true  = BasicBlock::Create(C, "unwind_true", &F);
      BasicBlock * unwind_false = BasicBlock::Create(C, "unwind_false", &F);
      
      IRBuilder <> B(unwind_entry);
      
      DISubprogram *SP = F.getSubprogram();
      DebugLoc DL = DILocation::get(SP->getContext(), SP->getLine(), 1, SP);
      B.SetCurrentDebugLocation(DL);

      B.CreateCall(potentialJump, {BlockAddress::get( resume_parent_unwind )});

#if 1
      Constant * SAVECONTEXT = Get__unwindrts_savecontext(*M);
#else
      Constant * SAVECONTEXT = Get_savecontext(*M);
#endif
      Constant * EXIT = Get_exit(*M);
      
      //Value * result = B.CreateCall(EXIT,  {ZERO});
      Value * result = B.CreateCall(SAVECONTEXT);
    

      Value * isEqOne = B.CreateICmpEQ(result, ONE);
      B.CreateCondBr(isEqOne, unwind_true, unwind_false);

      B.SetInsertPoint(unwind_true);
      B.CreateCall(EXIT, {ZERO});
      //B.CreateUnreachable();
      B.CreateBr(unwind_false);

      B.SetInsertPoint(unwind_false);

      if(F.getReturnType()->isVoidTy())
          B.CreateRetVoid();
      else if (F.getReturnType()->isIntegerTy())
          B.CreateRet(ZERO);
      else
          assert(0 && "Return type not supported yet");

      builder.SetInsertPoint(entryBB->getTerminator());
      builder.CreateCall(potentialJump, {BlockAddress::get(unwind_entry)});


#if 1
      // TODO : Inline be move to the Post Processing, when everything is complete 
      llvm::InlineFunctionInfo ifi;
      if(llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true)){
          errs() << "Able to inline function\n";
      } else {
          errs() << "UnableAble to inline function\n";
      }
#endif
      M->StealHandlerExists[unwind_entry] = true;
  }

  // --------------------------------------------------------------
  // Count the number of children
  int nChild = 1; // Oldest child
  for (auto pBB : bbV2CloneUNWIND){
      if( isa<DetachInst>(pBB->getTerminator()) ){
          nChild++;
      }
  }

  // Create the join counter
  builder.SetInsertPoint(entryBB->getFirstNonPHIOrDbgOrLifetime());
  joinCntrUNWIND = builder.CreateAlloca(Int32Ty, DL.getAllocaAddrSpace(), nullptr, "joincntr");
  Value * nChildIR = ConstantInt::get(Int32Ty, nChild, /*isSigned=*/false);
  

  return;
}

void UNWINDABI::postProcessFunction(Function &F) {

    Module * M = F.getParent();
    LLVMContext& C = M->getContext();
    BasicBlock & entry  = F.getEntryBlock();
    IRBuilder<> B(entry.getFirstNonPHIOrDbgOrLifetime());

    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);
  
    // Add enauli at the beginning of a function
    Constant * ENAULI = Get_ENAULI(*M);

    Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  
    Value *ZERO32 = ConstantInt::get(Int32Ty, 0x0, /*isSigned=*/false);  

    
    // Make sure to add DISULI at the end of a function
    // Get all the exit block and put DISULI before return
    for (auto &BB : F){
        Instruction * termInst = BB.getTerminator();
        if(isa<ReturnInst>(termInst)){
            B.SetInsertPoint(termInst);
            //Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);
            Constant * DISULI = Get_DISULI(*M);

            Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  
        }
    }

    return;
}

void UNWINDABI::postProcessHelper(Function &F) {
    //assert(false);
}

bool UNWINDABILoopSpawning::processLoop() {
    //assert(false);
  return false;
}

UNWINDABI::UNWINDABI() {}

