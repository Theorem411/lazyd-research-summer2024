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

#include "llvm/IR/IntrinsicInst.h"
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
using namespace llvm;

#define DEBUG_TYPE "unwindabi"

// Map from basic block and instruction in fast path to got stolen handler
static SmallVector<CallInst*,2> callInstV;
static ValueToValueMapTy VMapUNWINDGH;
static ValueToValueMapTy VMapSlowPath; 
static BasicBlock* slowPathPrologue;
static BasicBlock* slowPathEpilogue;
static BasicBlock* unwindPathEntry;
static BasicBlock* stolenHandlerPathEntry;
static BasicBlock* slowPathFcn;
static BasicBlock* restorePath;

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
DEFAULT_GET_LIB_FUNC(exit)

using mysetjmp_callee_ty = int (void**);
DEFAULT_GET_LIB_FUNC(mysetjmp_callee)

using mylongjmp_callee_ty = void (void**);
DEFAULT_GET_LIB_FUNC(mylongjmp_callee)

using savecontext_ty = int (void**);
DEFAULT_GET_LIB_FUNC(savecontext)

using resume2scheduler_ty = void (void );
DEFAULT_GET_LIB_FUNC(resume2scheduler)

using suspend2scheduler_ty = void (int * );
DEFAULT_GET_LIB_FUNC(suspend2scheduler)

using initworkers_env_ty = void (void );
DEFAULT_GET_LIB_FUNC(initworkers_env)

using deinitworkers_env_ty = void (void );
DEFAULT_GET_LIB_FUNC(deinitworkers_env)

using isunwind_triggered_ty = int (void);
DEFAULT_GET_LIB_FUNC(isunwind_triggered)

using initiate_unwindstack_ty = void (void);
DEFAULT_GET_LIB_FUNC(initiate_unwindstack)

using deinitperworkers_sync_ty = void(int, int);
DEFAULT_GET_LIB_FUNC(deinitperworkers_sync)

using initperworkers_sync_ty = void(int, int);
DEFAULT_GET_LIB_FUNC(initperworkers_sync)

using unwind_poll_ty = int(void);

#define UNWINDRTS_FUNC(name, CGF) Get__unwindrts_##name(CGF)

static GlobalVariable* GetGlobalVariable(const char* GlobalName, Type* GlobalType, Module& M, bool localThread=false){    
  GlobalVariable* globalVar = M.getNamedGlobal(GlobalName);
  if(globalVar){
      return globalVar;
  }
  
  globalVar = dyn_cast<GlobalVariable>(M.getOrInsertGlobal(GlobalName, GlobalType));
  globalVar->setLinkage(GlobalValue::ExternalLinkage);  
  if(localThread)
      globalVar->setThreadLocal(true);

  return globalVar; 
}

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
  if (Fn)
    return true;

  // Otherwise we have to create it
  FunctionType *FTy = TypeBuilder<T, false>::get(Ctx);
  Fn = Function::Create(FTy, Linkage, FnName, &M);

  // Set nounwind if it does not throw.
  if (DoesNotThrow)
    Fn->setDoesNotThrow();

  return false;
}

/*
  Refer to uli/cas_ws/lib/unwind_scheduler.h mysetjmp_callee
*/
static Function* Get__unwindrts_mysetjmp_callee(Module& M) {
    // Inline assembly to move the callee saved regist to rdi
    Function* Fn = nullptr;
    if (GetOrCreateFunction<mysetjmp_callee_ty>("mysetjmp_callee_llvm", M, Fn))
        return Fn;

    LLVMContext& Ctx = M.getContext();

    BasicBlock* Entry                 = BasicBlock::Create(Ctx, "mysethjmp.entry", Fn);
    BasicBlock* NormalExit            = BasicBlock::Create(Ctx, "normal.exit", Fn);
    BasicBlock* ThiefExit             = BasicBlock::Create(Ctx, "thief.exit", Fn);

    Type* Int32Ty = TypeBuilder<int32_t, false>::get(Ctx);
    Value* ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);  
    Value* ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);  
    
    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;

    using AsmTypeCallee = void (void**);
    FunctionType *FAsmTypeCallee = TypeBuilder<AsmTypeCallee, false>::get(Ctx);

    Value *Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rdi\nmovq %rbp, 0(%rdi)\nmovq %rsp, 16(%rdi)\nmovq %rbx, 24(%rdi)\nmovq %r12, 32(%rdi)\nmovq %r13, 40(%rdi)\nmovq %r14, 48(%rdi)\nmovq %r15, 56(%rdi)\n", "r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    IRBuilder<> B(Entry);
    
    B.CreateCall(Asm, {argsCtx});
    //Value * loadIdx =  B.CreateConstGEP1_32(argsCtx, 1);   
    //B.CreateStore( BlockAddress::get(ThiefExit), loadIdx);
    
    auto OpaqueTrueTy = FunctionType::get(Type::getInt1Ty(Ctx), false);
    auto OpaqueTrue = InlineAsm::get(OpaqueTrueTy, "xor $0, $0",  "=r,~{dirflag},~{fpsr},~{flags}", false);
    Value* res = B.CreateCall(OpaqueTrue);
       
    B.CreateCondBr(res, ThiefExit, NormalExit);
    {
        B.SetInsertPoint(NormalExit);
        B.CreateRet(ZERO);
    }
    {        
        B.SetInsertPoint(ThiefExit);
        B.CreateRet(ONE);
    }

    return Fn;
}


/*
  Refer to uli/cas_ws/lib/unwind_scheduler.h unwind_poll
 */
static Function* Get__unwindrts_unwind_poll(Module& M) {
  Function* Fn = nullptr;
  if (GetOrCreateFunction<unwind_poll_ty>("unwind_poll_llvm", M, Fn))
    return Fn;
  LLVMContext& Ctx = M.getContext();
  
  BasicBlock* PollEntry = BasicBlock::Create(Ctx, "poll.entry", Fn);
  BasicBlock* StartUnwind = BasicBlock::Create(Ctx, "start.unwind", Fn);
  BasicBlock* ResumeParent = BasicBlock::Create(Ctx, "resume.parent", Fn);
  BasicBlock* InitiateUnwind = BasicBlock::Create(Ctx, "initiate.unwind", Fn); 

  IRBuilder<> B(PollEntry);
  
  Value *ONE = B.getInt32(1);
  Value *ZERO = B.getInt32(0);
  
  Constant *ISUNWINDTRIGGERED = Get_isunwind_triggered(M);

  Value *res1 = B.CreateCall(ISUNWINDTRIGGERED);                
  Value *isEqOne = B.CreateICmpEQ(res1, ONE);
  
  B.CreateCondBr(isEqOne, StartUnwind, ResumeParent);
  B.SetInsertPoint(StartUnwind);
  
  Constant *MYSETJMP_CALLEE = UNWINDRTS_FUNC(mysetjmp_callee, M);
  GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", TypeBuilder<workcontext_ty,false>::get(Ctx), M, true);
  Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );
  Value *res2 = B.CreateCall(MYSETJMP_CALLEE, {gunwind_ctx});
  isEqOne = B.CreateICmpEQ(res2, ONE);

  B.CreateCondBr(isEqOne, ResumeParent, InitiateUnwind);

  llvm::InlineFunctionInfo ifi;
  llvm::InlineFunction(dyn_cast<CallInst>(res2), ifi, nullptr, true);              
  
  B.SetInsertPoint(InitiateUnwind);
  Constant *INITIATEUNWINDSTACK = Get_initiate_unwindstack(M);
  B.CreateCall(INITIATEUNWINDSTACK);
  //Value* savedPc = B.CreateConstGEP1_32(gunwind_ctx, 1);   
  //B.CreateStore(BlockAddress::get(ResumeParent), savedPc);    
  B.CreateRet(ONE);

  B.SetInsertPoint(ResumeParent);
  B.CreateRet(ZERO);

  return Fn;    
}


/*
  Refer to uli/cas_ws/lib/unwind_scheduler.h mylongjmp_callee
*/
static Function *Get__unwindrts_mylongjmp_callee(Module& M) {
    Function* Fn = nullptr;
    if (GetOrCreateFunction<mylongjmp_callee_ty>("mylongjmp_callee_llvm", M, Fn))
        return Fn;

    LLVMContext& Ctx = M.getContext();

    BasicBlock* Entry           = BasicBlock::Create(Ctx, "mylongjmp.entry", Fn);    
    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;

    using AsmTypCallee = void ( void** );
    FunctionType *FAsmTypCallee = TypeBuilder<AsmTypCallee, false>::get(Ctx);

    Value *Asm = InlineAsm::get(FAsmTypCallee, "movq $0, %rdi\nmovq 0(%rdi), %rbp\nmovq 16(%rdi), %rsp\nmovq 24(%rdi), %rbx\nmovq 32(%rdi), %r12\nmovq 40(%rdi), %r13\nmovq 48(%rdi), %r14\nmovq 56(%rdi), %r15\njmpq *8(%rdi)", "r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    IRBuilder<> B(Entry);    
    B.CreateCall(Asm, argsCtx);
    B.CreateRetVoid();
    return Fn;
}

/// \brief Get or create a LLVM function for savecontext.
/// It is equivalent to the following C code
/// Refer to uli/cas_ws/lib/scheduler.c savecontext 
///
/// }
static Function *Get__unwindrts_savecontext(Module& M) {
  Function* Fn = nullptr;
  if (GetOrCreateFunction<savecontext_ty>("savecontext_llvm", M, Fn))
    return Fn;

  LLVMContext& Ctx = M.getContext();

  BasicBlock *Entry                 = BasicBlock::Create(Ctx, "unwind.entry", Fn);
  BasicBlock *ThiefEntry            = BasicBlock::Create(Ctx, "unwind.thief.entry", Fn);
  BasicBlock *AttemptUnwinding      = BasicBlock::Create(Ctx, "unwind.attempt.unwinding", Fn);
  BasicBlock *AttemptUnwindCont     = BasicBlock::Create(Ctx, "unwind.attempt.unwind.cont", Fn);
  BasicBlock *ReachTopStack         = BasicBlock::Create(Ctx, "unwind.reach.top.stack", Fn);
  BasicBlock *ReachAlreadyConverted = BasicBlock::Create(Ctx, "unwind.reach.already.converted", Fn);
  BasicBlock *AddrNull              = BasicBlock::Create(Ctx, "unwind.addr.null", Fn);
  BasicBlock *KeepUnwinding         = BasicBlock::Create(Ctx, "unwind.keep.unwinding", Fn);     
  BasicBlock *CheckRA               = BasicBlock::Create(Ctx, "unwind.check.RA", Fn);     
  BasicBlock *FinishUnwinding       = BasicBlock::Create(Ctx, "unwind.finish.unwinding", Fn);     

  Type *Int32Ty = TypeBuilder<int32_t, false>::get(Ctx);
  Value *ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
  Value *ONE_64T = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 1, /*isSigned=*/false);  
  Value *ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);  
  
  GlobalVariable* gSeed_ptr = GetGlobalVariable("seed_ptr", TypeBuilder<addr_ty*, false>::get(Ctx), M, true); 
  GlobalVariable* gThreadId = GetGlobalVariable("threadId", TypeBuilder<int, false>::get(Ctx), M, true); 
  GlobalVariable* gSeed_bp = GetGlobalVariable("seed_bp", TypeBuilder<addr_ty**, false>::get(Ctx), M);
  GlobalVariable* gUnwindRetAddr = GetGlobalVariable("unwindRetAddr", TypeBuilder<addr_ty, false>::get(Ctx), M, true);
  GlobalVariable* gGotstolenRetAddr = GetGlobalVariable("gotstolenRetAddr", TypeBuilder<addr_ty, false>::get(Ctx), M, true);
  GlobalVariable* gUnwindContext = GetGlobalVariable("unwindCtx", TypeBuilder<workcontext_ty, false>::get(Ctx), M, true);

  IRBuilder<> B(Entry);
  {
      
      ///    unsigned ptr = (seed_ptr - seed_bp[threadId]);      
      Value * gSeed_bpVal = B.CreateLoad(gSeed_bp);    
      Value * gThreadIdVal = B.CreateLoad(gThreadId);
      Value * gSeed_ptrVal = B.CreateLoad(gSeed_ptr);      

      Value * bp_location = B.CreateInBoundsGEP(gSeed_bpVal, gThreadIdVal); 
      Value * gSeed_bpEntry = B.CreateLoad(bp_location);    
      Value* seedOffset = B.CreatePtrDiff(gSeed_ptrVal, gSeed_bpEntry);

      ///    void ** ctx  = (void**) workctx_arr[threadId][ptr]; 
      Function::arg_iterator args = Fn->arg_begin();
      Value* loadIdx1bitcast = &*args;
      
      Constant* MYSETJMP_CALLEE = UNWINDRTS_FUNC(mysetjmp_callee, M);
      Constant* MYLONGJMP_CALLEE = UNWINDRTS_FUNC(mylongjmp_callee, M);
      Value * unwindCtxLoad = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );

      // seed_ptr = 0;
      Value * addPtr = B. CreateConstGEP1_32(gSeed_ptrVal,  0);
      B.CreateStore(addPtr, gSeed_ptr);              
      
      Value* result = B.CreateCall(MYSETJMP_CALLEE, {loadIdx1bitcast});  
      dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);      
      
      Value * isEqOne = B.CreateICmpEQ(result, ONE);        
      B.CreateCondBr(isEqOne, ThiefEntry, AttemptUnwinding);
      
      //Thief entry
      {
          B.SetInsertPoint(ThiefEntry);
          B.CreateRet(ONE);
      }

      // Keep unwinding
      {
          B.SetInsertPoint(AttemptUnwinding);
          // Create another basic block that exits
      
          // void** addrRA = ((void**)*(seed_ptr)); 
          // *addrRa = gotStolenRetAddr;
          Value* pSeedLoad = B.CreateLoad(gSeed_ptr);
          Value* pSeedLoadAdd = B. CreateConstGEP1_32(pSeedLoad,  0);
          Value* seedLoad = B.CreateLoad(pSeedLoadAdd);
          Value* pPseedLoad = B.CreateBitCast(seedLoad, TypeBuilder<addr_ty*, false>::get(Ctx));
          //Value* addrRa = B.CreateLoad(pPseedLoad);
          Value* loadGotStolenAddr = B.CreateLoad(gGotstolenRetAddr);                            
          B.CreateStore(loadGotStolenAddr, pPseedLoad);

          Value* isEqOne = B.CreateICmpEQ(seedOffset, ONE_64T);
          B.CreateCondBr(isEqOne, ReachTopStack, AttemptUnwindCont);
          
          // Reach top of stack
          {
              B.SetInsertPoint(ReachTopStack);
              B.CreateBr(FinishUnwinding);
          }
          
          // Attempt Keep unwinding
          {
              B.SetInsertPoint( AttemptUnwindCont);            

              Value * addPtr = B. CreateConstGEP1_32(gSeed_ptrVal,  -1);
              B.CreateStore(addPtr, gSeed_ptr);        
      
              Value * addPtrVal = B.CreateLoad(addPtr);
              Value * addBitCastVal = B.CreateBitCast(addPtrVal, addPtrVal->getType()->getPointerTo());

              Value * pred1 = B.CreateICmpEQ( addBitCastVal, 
                                              ConstantPointerNull::get(dyn_cast<PointerType>(addBitCastVal->getType())));              
              B.CreateCondBr(pred1, AddrNull, CheckRA);

              B.SetInsertPoint(AddrNull);
              B.CreateBr(FinishUnwinding);
              
              B.SetInsertPoint(CheckRA);
              Value * loadAddr1  = B.CreateLoad(addBitCastVal);
              Value * loadUnwindAddr1 = B.CreateLoad(gUnwindRetAddr);              
              Value * pred2 = B.CreateICmpEQ(loadAddr1, loadUnwindAddr1);                           

              B.CreateCondBr(pred2, KeepUnwinding, ReachAlreadyConverted);
              {
                  B.SetInsertPoint( ReachAlreadyConverted );
                  B.CreateBr(FinishUnwinding);
              }

              {
                  B.SetInsertPoint( KeepUnwinding );           
                  B.CreateRet(ZERO);
              }
          }
          
          // Finish Unwinding
          {
              B.SetInsertPoint(FinishUnwinding);
              Value * result = B.CreateCall(MYLONGJMP_CALLEE, {unwindCtxLoad});
              dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);
              llvm::InlineFunctionInfo ifi;
              llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);
              B.CreateBr(ThiefEntry);
          }
      }

      llvm::InlineFunctionInfo ifi;
      llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);

  }  
  Fn->addFnAttr(Attribute::InlineHint);
  return Fn;
}

void UNWINDABI::createSync(SyncInst &SI, ValueToValueMapTy &DetachCtxToStackFrame) {         
    
    // Fast Path
    // ----------------------------------------------
    {
        if(!callInstV.empty()) {
            BasicBlock * succ = SI.getSuccessor(0);        
            IRBuilder<> B(succ->getFirstNonPHIOrDbgOrLifetime());        
            CallInst* CI = callInstV.front();
            Function * fcn = CI->getCalledFunction();
        
            auto phiNode = B.CreatePHI(fcn->getReturnType(), 2);  
            for (auto it = pred_begin(succ), et = pred_end(succ); it!=et; ++it){
                BasicBlock* pred = *it;
            
                if(pred == callInstV.front()->getParent()){
                    phiNode->addIncoming(callInstV.front(), callInstV.front()->getParent());
                } else {
                    phiNode->addIncoming(callInstV.back(), pred);
                }
            
            }
           
            Value::use_iterator UI = CI->use_begin(), E = CI->use_end();
            for (; UI != E;) {
                Use &U = *UI;
                ++UI;
                auto *Usr = dyn_cast<Instruction>(U.getUser());
                if (Usr && !isa<PHINode>(Usr) && Usr->getParent() == succ )            
                    U.set(phiNode);
            }
        }
    }    
    return;
}

void UNWINDABI::createGotStolenHandler(DetachInst& Detach) {
    BasicBlock* curBB = Detach.getParent();
    Function* F = curBB->getParent();
    Module* M = F->getParent();
    
    Constant* suspend2scheduler = Get_suspend2scheduler(*M);
    Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);

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
    stolenHandlerPathEntry = CloneBasicBlock(detachBB, VMapUNWINDGH, ".gotstolen", F, nullptr, &DIFinder);
    VMapUNWINDGH[detachBB] = stolenHandlerPathEntry;        
     
    // --------------------------------------------------------------
    // Remap the cloned instruction
    for (Instruction &II : *stolenHandlerPathEntry) {
        RemapInstruction(&II, VMapUNWINDGH, RF_IgnoreMissingLocals, nullptr, nullptr);
    }

    // Add potential jump from detachBB to got stolen handler
    // Add potential jump after "spawn to fib" to avoid merging the gotstolen handler and the detachBlock
    IRBuilder<> builder(detachBB->getTerminator()); 
    builder.CreateCall(potentialJump, {BlockAddress::get( stolenHandlerPathEntry )});        
    builder.SetInsertPoint(stolenHandlerPathEntry->getTerminator());
        
    // Perform synchronizatoin here        
    builder.CreateCall(suspend2scheduler, {ConstantPointerNull::get(builder.getInt32Ty()->getPointerTo())});        

    Instruction* iterm = stolenHandlerPathEntry->getTerminator();                
    BranchInst* resumeBr = BranchInst::Create(unwindPathEntry);
    ReplaceInstWithInst(iterm, resumeBr);

    //Split basic block here. Used as hack to reload join counter in -0O
    //stolenHandlerPathEntry->splitBasicBlock(stolenHandlerPathEntry->getTerminator()->getPrevNode());

    for( Instruction &II : *detachBB){
        if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->hasFnAttribute(Attribute::Forkable)){
            
            // Associate callsite instruction with got-stolen handler
            M->CallStealMap[&II].stolenHandler = stolenHandlerPathEntry;          
            break;
        }
    } 
    M->StolenHandlerExists[stolenHandlerPathEntry] = true;
}

void UNWINDABI::createSlowPathFcn(DetachInst& Detach) {
    BasicBlock* curBB = Detach.getParent();
    Function* F = curBB->getParent();    

    static ValueToValueMapTy VMapSlowPath; 
    DebugInfoFinder DIFinder;      
    DISubprogram *SP = F->getSubprogram();
    if (SP) {
        //assert(!MustCloneSP || ModuleLevelChanges);
        // Add mappings for some DebugInfo nodes that we don't want duplicated
        // even if they're distinct.
        auto &MD = VMapSlowPath.MD();
        MD[SP->getUnit()].reset(SP->getUnit());
        MD[SP->getType()].reset(SP->getType());
        MD[SP->getFile()].reset(SP->getFile());  
        MD[SP].reset(SP); 
    }        
    
    // Perform the actual cloning
    BasicBlock * contBB = Detach.getContinue(); 
    slowPathFcn = CloneBasicBlock(contBB, VMapSlowPath, ".slowPath", F, nullptr, &DIFinder);
    VMapSlowPath[contBB] = slowPathFcn;        
     
    // --------------------------------------------------------------
    // Remap the cloned instruction
    for (Instruction &II : *slowPathFcn) {
        RemapInstruction(&II, VMapSlowPath, RF_IgnoreMissingLocals, nullptr, nullptr);        
    }

    for(Instruction &II : *contBB) {
        // Look for potential call
        if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->hasFnAttribute(Attribute::Forkable) 
           && !dyn_cast<CallInst>(&II)->getCalledFunction()->getReturnType()->isVoidTy()) {
            callInstV.push_back(dyn_cast<CallInst>(&II));
            callInstV.push_back(dyn_cast<CallInst>(VMapSlowPath[&II]));
        } 
    }

    Instruction* itermSlowPathPrologue = slowPathPrologue->getTerminator();  
    Instruction* itermSlowPathFcn =slowPathFcn->getTerminator();
    
    BranchInst* resume2SlowPathFcn = BranchInst::Create(slowPathFcn);
    BranchInst* resume2slowPathEpilogue = BranchInst::Create(slowPathEpilogue);        

    ReplaceInstWithInst(itermSlowPathPrologue, resume2SlowPathFcn);
    ReplaceInstWithInst(itermSlowPathFcn, resume2slowPathEpilogue);
}

void UNWINDABI::createFastPath(DetachInst& Detach) {
    // Add the prologue at beginning of the deattach block
    BasicBlock* curBB = Detach.getParent();
    Function* F = curBB->getParent();
    Module* M = F->getParent();
    LLVMContext& C = M->getContext();

    BasicBlock* bb = nullptr;
    Instruction* term = nullptr;
    SmallVector<BasicBlock*, 8> bbList;
    DenseMap<BasicBlock *, bool> haveVisited;

    BasicBlock* detachBB = Detach.getDetached();        
    Value* OneByte = ConstantInt::get(IntegerType::getInt64Ty(C), 8, false);

    // Common Used Function
    Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
    Function* getSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);

    Constant* PUSH_SS = Get_push_ss(*M);
    Constant* POP_SS = Get_pop_ss(*M);

    IRBuilder<> fastBuilder(detachBB->getFirstNonPHIOrDbgOrLifetime()); 
        
    // Build the Fast Path Prologue
    // push_ss((void*) (builtin_sp() - 8) );
    Value * SPVal = fastBuilder.CreateCall(getSP);
    Value * SPValInt = fastBuilder.CreateCast(Instruction::PtrToInt, SPVal, IntegerType::getInt64Ty(C));
    Value * ppRA  = fastBuilder.CreateSub(SPValInt, OneByte);
    ppRA = fastBuilder.CreateCast(Instruction::IntToPtr, ppRA, IntegerType::getInt8Ty(C)->getPointerTo());
    fastBuilder.CreateCall(PUSH_SS, {ppRA});

    fastBuilder.CreateCall(potentialJump, {BlockAddress::get( unwindPathEntry )});
        
    for( Instruction &II : *detachBB){
        if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->hasFnAttribute(Attribute::Forkable) ){
            // Associate callsite instruction with steal handler
            M->CallStealMap[&II].stealHandler = slowPathPrologue;
            // Associate callsite instruction with unwind handler
            M->CallStealMap[&II].unwindHandler = unwindPathEntry;
            // Indicate the steal hander basic block needs a label
            M->StealHandlerExists[M->CallStealMap[&II].stealHandler] = true;                    
            break;
        }
    }

    bbList.clear();
    haveVisited.clear();
    // Look for the reattach inst
    // Add an epilogue just before it (POP_SS)
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

Function* UNWINDABI::createDetach(DetachInst &Detach,
                        ValueToValueMapTy &DetachCtxToStackFrame,
                        DominatorTree &DT, AssumptionCache &AC) {
    // GotStolen Handler
    createGotStolenHandler(Detach);

    // Temporary solution
    createSlowPathFcn(Detach);

    // Create the Fast Path
    createFastPath(Detach);
    return NULL;
}

void UNWINDABI::createRestorePath(Function& F, SyncInst * SI) {
    IRBuilder <> B(restorePath);    

    // Restore path
    B.CreateBr(SI->getSuccessor(0));

}

void UNWINDABI::createUnwindHandler(Function& F) {
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();
    
    BasicBlock* unwindSaveCtx = BasicBlock::Create(C, "unwind.save.ctx", &F);      
    IRBuilder<> B(unwindPathEntry);
      
    DISubprogram* SP = F.getSubprogram();
    DebugLoc DL = DILocation::get(SP->getContext(), SP->getLine(), 1, SP);
    B.SetCurrentDebugLocation(DL);

    Value* ONE = B.getInt32(1);
    Value* ZERO = B.getInt32(0);

    GlobalVariable* gSeed_ptr = GetGlobalVariable("seed_ptr", TypeBuilder<addr_ty*, false>::get(C), *M, true); 
    GlobalVariable* gThreadId = GetGlobalVariable("threadId", TypeBuilder<int, false>::get(C), *M, true); 
    GlobalVariable* gSeed_bp = GetGlobalVariable("seed_bp", TypeBuilder<addr_ty**, false>::get(C), *M);       
    GlobalVariable* gWorkContext = GetGlobalVariable("workctx_arr", 
                                                       TypeBuilder<workcontext_ty,false>::get(C)->getPointerTo()->getPointerTo(), *M);
    
    ///    unsigned ptr = (seed_ptr - seed_bp[threadId]);      
    Value* gThreadIdVal = B.CreateLoad(gThreadId);
    Value* gSeed_bpVal = B.CreateLoad(gSeed_bp);        
    Value* bp_location = B.CreateInBoundsGEP(gSeed_bpVal, gThreadIdVal); 
    Value* gSeed_bpEntry = B.CreateLoad(bp_location);    
  
    Value* gSeed_ptrVal = B.CreateLoad(gSeed_ptr);      
    Value* seedOffset = B.CreatePtrDiff(gSeed_ptrVal, gSeed_bpEntry);

    Value* workCtxLoad = B.CreateLoad(gWorkContext);
    Value* idx2 = B.CreateInBoundsGEP(workCtxLoad, gThreadIdVal);
    Value* loadIdx2 = B.CreateLoad(idx2 );
    Value* idx1 = B.CreateInBoundsGEP(loadIdx2, seedOffset);
    Value* loadIdx1bitcast = B.CreateConstInBoundsGEP2_64(idx1, 0, 0);
    
    Value* savedPc = B.CreateConstGEP1_32(loadIdx1bitcast, 1);   
    B.CreateStore(BlockAddress::get(slowPathPrologue), savedPc);    
  
    Constant* SAVECONTEXT = UNWINDRTS_FUNC(savecontext, *M);
    Value* result = B.CreateCall(SAVECONTEXT, {loadIdx1bitcast});        
    
    Value* isEqOne = B.CreateICmpEQ(result, ONE);
    B.CreateCondBr(isEqOne, slowPathPrologue, unwindSaveCtx);

    B.SetInsertPoint(unwindSaveCtx);

    if(F.getReturnType()->isVoidTy())
        B.CreateRetVoid();
    else if (F.getReturnType()->isIntegerTy())
        B.CreateRet(ZERO);
    else
        assert(0 && "Return type not supported yet");

    M->StealHandlerExists[unwindPathEntry] = true;

    // TODO : Inline be move to the Post Processing, when everything is complete 
    llvm::InlineFunctionInfo ifi;
    llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);
}

void UNWINDABI::instrumentMainFcn(Function& F) {
    // Initialize the PRSC at the beginning of main
    Module* M = F.getParent();
    IRBuilder<> B(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

    Constant* INITWORKERS_ENV = Get_initworkers_env(*M);
    Constant* DEINITWORKERS_ENV = Get_deinitworkers_env(*M);
    Constant* INITPERWORKERS_SYNC = Get_initperworkers_sync(*M);
    Constant* DEINITPERWORKERS_SYNC = Get_deinitperworkers_sync(*M);

    Value* ONE = B.getInt32(1);
    Value* ZERO = B.getInt32(0);

    // Get debug info
    DISubprogram *SP = F.getSubprogram();
    DebugLoc DL = DILocation::get(SP->getContext(), SP->getLine(), 1, SP);
    B.SetCurrentDebugLocation(DL);
    B.CreateCall(INITWORKERS_ENV);
    B.CreateCall(INITPERWORKERS_SYNC,  {ZERO, ONE});   

    for (auto &BB : F){
        Instruction * termInst = BB.getTerminator();
        if(isa<ReturnInst>(termInst)){
            B.SetInsertPoint(termInst);
            B.CreateCall(DEINITPERWORKERS_SYNC, {ZERO, ONE});
            B.CreateCall(DEINITWORKERS_ENV);
        }
    }   
}

void UNWINDABI::instrumentSpawningFcn(Function& F) {
    Module* M = F.getParent();
    LLVMContext &Ctx = M->getContext();
    IRBuilder<> B(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

    Value *ONE = B.getInt32(1);
    Value *ZERO = B.getInt32(0);

    Constant* UNWIND_POLL = UNWINDRTS_FUNC(unwind_poll, *M);    

    // Get debug info
    DISubprogram *SP = F.getSubprogram();
    DebugLoc DL = DILocation::get(SP->getContext(), SP->getLine(), 1, SP);
    B.SetCurrentDebugLocation(DL);

    Value* res = B.CreateCall(UNWIND_POLL);    
    Instruction* isEqOne = dyn_cast<Instruction>(B.CreateICmpEQ(res, ONE));
    BasicBlock *returnToUnwindBB = BasicBlock::Create(Ctx, "returnto.unwind", &F);

    BasicBlock* afterBB = F.getEntryBlock().splitBasicBlock(isEqOne->getNextNode());
    auto branch = BranchInst::Create(returnToUnwindBB, afterBB, isEqOne);
    
    auto terminator = F.getEntryBlock().getTerminator();    
    ReplaceInstWithInst(terminator, branch);

    llvm::InlineFunctionInfo ifi;
    llvm::InlineFunction(dyn_cast<CallInst>(res), ifi, nullptr, true);
    
    B.SetInsertPoint(returnToUnwindBB);
    GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", TypeBuilder<workcontext_ty,false>::get(Ctx), *M, true);
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );
    Value* savedPc = B.CreateConstGEP1_32(gunwind_ctx, 1);   
    B.CreateStore(BlockAddress::get(afterBB), savedPc);     
    if(F.getReturnType()->isVoidTy())
        B.CreateRetVoid();
    else if (F.getReturnType()->isIntegerTy())
        B.CreateRet(ZERO);
    else
        assert(0 && "Return type not supported yet");
    
    for (auto &BB : F){
        Instruction * termInst = BB.getTerminator();
        if(isa<ReturnInst>(termInst)){            
            B.SetInsertPoint(termInst);
            Value* res = B.CreateCall(UNWIND_POLL);

            Instruction* isEqOne = dyn_cast<Instruction>(B.CreateICmpEQ(res, ONE));
            BasicBlock *returnToUnwindBB = BasicBlock::Create(Ctx, "returnto.unwind2", &F);

            BasicBlock* afterBB = BB.splitBasicBlock(isEqOne->getNextNode());
            auto branch = BranchInst::Create(returnToUnwindBB, afterBB, isEqOne);
    
            auto terminator = BB.getTerminator();    
            ReplaceInstWithInst(terminator, branch);
    
            llvm::InlineFunctionInfo ifi;
            llvm::InlineFunction(dyn_cast<CallInst>(res), ifi, nullptr, true);
    

            B.SetInsertPoint(returnToUnwindBB);
            Value* savedPc = B.CreateConstGEP1_32(gunwind_ctx, 1);   
            B.CreateStore(BlockAddress::get(afterBB), savedPc);    
  
            
            if(F.getReturnType()->isVoidTy())
                B.CreateRetVoid();
            else if (F.getReturnType()->isIntegerTy())
                B.CreateRet(ZERO);
            else
                assert(0 && "Return type not supported yet");

            break;
        }
    }   

}

Value* UNWINDABI::createSlowPathPrologue(Function& F) {
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();
    IRBuilder <> B(slowPathPrologue);

    using AsmTypCallee = void** ( void );
    FunctionType *FAsmTypCallee = TypeBuilder<AsmTypCallee, false>::get(C);
    Value* Asm = InlineAsm::get(FAsmTypCallee, "movq %rdi, $0\n", "=r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);    
    Value* workCtx = B.CreateCall(Asm);

    B.CreateBr(slowPathEpilogue);

    return workCtx;
}

void UNWINDABI::createSlowPathEpilogue(Function& F, Value* workCtx) {    
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();    

    IRBuilder <> B(slowPathEpilogue);    
    DISubprogram *SP = F.getSubprogram();
    DebugLoc DL = DILocation::get(SP->getContext(), SP->getLine(), 1, SP);
    B.SetCurrentDebugLocation(DL);   
    B.SetCurrentDebugLocation(B.getCurrentDebugLocation());
    
    Value* ONE = B.getInt32(1);
   
    Constant* MYSETJMP_CALLEE = UNWINDRTS_FUNC(mysetjmp_callee, *M);
    Value* result = B.CreateCall(MYSETJMP_CALLEE, {workCtx});
    dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);    
    
    Value* savedPc =  B.CreateConstGEP1_32(workCtx, 1);   
    B.CreateStore( BlockAddress::get(restorePath), savedPc);    

    Value* isEqOne = B.CreateICmpEQ(result, ONE);           
    BasicBlock* suspendPath = BasicBlock::Create(C, "suspend.path", &F);
    B.CreateCondBr(isEqOne, restorePath, suspendPath);    
    
    llvm::InlineFunctionInfo ifi;
    llvm::InlineFunction(dyn_cast<CallInst>(result), ifi);

    B.SetInsertPoint(suspendPath);                       
    Function* resume2scheduler = dyn_cast<Function>(M->getOrInsertFunction( "resume2scheduler", TypeBuilder<void (void**) , false>::get(M->getContext())));
    B.CreateCall(resume2scheduler, {workCtx});
    B.CreateBr(restorePath);        
}

void UNWINDABI::preProcessFunction(Function &F) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> builder(C);

  // Add Thread initialization and deinitialization on the main function
  // TODO : Make this optional
  if ( F.getName() == "main") {
      instrumentMainFcn(F); 
      return;
  }
  
  // -------------------------------------------------
  // Add forkable attribute
  for (auto &BB : F){
      if (DetachInst * DI = dyn_cast<DetachInst>(BB.getTerminator())){          
          BasicBlock * detachBlock = dyn_cast<DetachInst>(DI)->getDetached();
          for( Instruction &II : *detachBlock ) {
              if( isa<CallInst>(&II)  && !isa<DbgInfoIntrinsic>(&II)) {
                  dyn_cast<CallInst>(&II)->getCalledFunction()->addFnAttr(Attribute::Forkable);               
              }
          }
      }
  }

  // Insert polling in prologue and epilogue
  instrumentSpawningFcn(F);

  // -------------------------------------------------------------
  // Create the resume path
  for (auto &BB : F){
      if( SyncInst *SI = dyn_cast<SyncInst>(BB.getTerminator()) ){
          slowPathEpilogue = BasicBlock::Create(C, "slow.path.epilogue", &F);
          slowPathPrologue = BasicBlock::Create(C, "slow.path.prologue", &F);    
          unwindPathEntry = BasicBlock::Create(C, "unwind.path.entry", &F);
          restorePath = BasicBlock::Create(C, "restore.path", &F);

          createRestorePath(F, SI);
          Value* workCtx = createSlowPathPrologue(F);
          createSlowPathEpilogue(F, workCtx);
          createUnwindHandler(F);
      }
  }  
  return;
}


void UNWINDABI::postProcessFunction(Function &F) {
    return;
}

void UNWINDABI::postProcessHelper(Function &F) {
  return;
}

bool UNWINDABILoopSpawning::processLoop() {
  return false;
}

Value *UNWINDABI::lowerGrainsizeCall(CallInst *GrainsizeCall) {
  assert(false);
  return nullptr;
}

UNWINDABI::UNWINDABI() {}

