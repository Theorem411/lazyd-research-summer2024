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

//TODO : Bug in -O0 in fib_sp
//TODO : Proper Stacklet in runtime
//TODO : Code refactoring
//TODO : Design document
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
    
    //Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);
    //Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);


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
        //fastBuilder.CreateCall(enauli, {NEG_ZERO}); 
        //fastBuilder.CreateCall(ENAULI); 
        fastBuilder.CreateCall(PUSH_SS, {ppRA});


        // Book Keeping
        startOfStealHandler = continueBB;
        for( Instruction &II : *detachBB){
            if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->hasFnAttribute(Attribute::Forkable) ){
                BasicBlock * stealhandler = dyn_cast<BasicBlock>(VMapUNWIND[startOfStealHandler]);                    
                // Associate callsite instruction with steal handler
                M->CallStealMap[&II].stealHandler = stealhandler;
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
                //fastBuilder.CreateCall(disuli, { ZERO });
                fastBuilder.CreateCall(ENAULI);


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
              B.CreateCall(SetupRBPfromRSP);
              B.CreateCall(DEC_SS);
              B.CreateBr(SI->getSuccessor(0));
              
              // Add a potential jump from entry to resume_parent_unwind block
              builder.SetInsertPoint(entryBB->getTerminator());
              builder.CreateCall(potentialJump, {BlockAddress::get(resume_parent_unwind)});

          }
      }
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
  builder.CreateStore(nChildIR,  joinCntrUNWIND);
  
  return;
}

void UNWINDABI::postProcessFunction(Function &F) {
    // TODO
    // Find all alloca instruction.
    // Compute blocks that they are live in
    // Reload those live variables if they are live in a steal handler
    // lib/Transforms/Utils/PromoteMemoryToRegister.cpp ComputeLiveIn

    Module * M = F.getParent();
    LLVMContext& C = M->getContext();
    BasicBlock & entry  = F.getEntryBlock();
    IRBuilder<> B(entry.getFirstNonPHIOrDbgOrLifetime());

    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);
  
    // Add enauli at the beginning of a function
    //Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);
    Constant * ENAULI = Get_ENAULI(*M);

    Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  
    Value *ZERO32 = ConstantInt::get(Int32Ty, 0x0, /*isSigned=*/false);  
    //B.CreateCall(enauli, { NEG_ZERO });
    B.CreateCall(ENAULI);

    
    // Make sure to add DISULI at the end of a function
    // Get all the exit block and put DISULI before return
    for (auto &BB : F){
        Instruction * termInst = BB.getTerminator();
        if(isa<ReturnInst>(termInst)){
            B.SetInsertPoint(termInst);
            //Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);
            Constant * DISULI = Get_DISULI(*M);

            Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  
            //B.CreateCall(disuli, { ZERO });
            B.CreateCall(DISULI);
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

