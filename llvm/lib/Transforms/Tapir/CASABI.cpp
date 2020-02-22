//===- CASABI.cpp - Lower Tapir into CAS PRSC runtime system calls -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the CAS ABI to convert Tapir instructions to calls
// into the user-level-interrupts PRSC library.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Tapir/CASABI.h"
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

#define DEBUG_TYPE "casabi"

// Map from basic block and instruction in fast path to slow path
ValueToValueMapTy VMap;
// Map from basic block and instruction in fast path to got stolen handler
ValueToValueMapTy VMapGH; 
// Contain original fast path
SmallVector<BasicBlock*, 8> bbV2Clone;


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


using PUSH_SS_ty = void (void *);
DEFAULT_GET_LIB_FUNC(PUSH_SS)

using POP_SS_ty = void (void );
DEFAULT_GET_LIB_FUNC(POP_SS)

using DEC_SS_ty = void (void );
DEFAULT_GET_LIB_FUNC(DEC_SS)

//using RESUME2SCHEDULER_ty = void (void * , void * , void *, long, long, int * );
//DEFAULT_GET_LIB_FUNC(RESUME2SCHEDULER);

Value *CASABI::lowerGrainsizeCall(CallInst *GrainsizeCall) {
  assert(false);
  return nullptr;
}

void CASABI::createSync(SyncInst &SI, ValueToValueMapTy &DetachCtxToStackFrame) {    
    SyncInst* syncClone = dyn_cast<SyncInst>(VMap[&SI]);
    
    BasicBlock * curBB = SI.getParent();
    Function * F = curBB->getParent();
    Module * M = F->getParent();
    LLVMContext& C = M->getContext();
    
    BasicBlock * bb = nullptr;
    Instruction * term = nullptr;
    
    // Build type
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);

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


        // Look for the reattach inst
        // Add an epilogue just before it
        bbList.push_back(syncBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator() ))  ){
                // Don't push anymore if we encountered reattach instruction
                ReattachInst * reattachInst = dyn_cast<ReattachInst>( bb->getTerminator() );
                BasicBlock   * startOfStealHandler = reattachInst->getDetachContinue();
                slowBuilder.SetInsertPoint( startOfStealHandler->getFirstNonPHIOrDbgOrLifetime() );
                
                //slowBuilder.CreateCall(RESUME2SCHEDULER, {NEG_ZERO});
            } else {
                for( pred_iterator PI = pred_begin(bb); PI!=pred_end(bb); PI++ ){                
                    bbList.push_back(*PI);
                }
            }
        }

    }

    return;
}


Function *CASABI::createDetach(DetachInst &Detach,
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
    Constant * PUSH_SS = Get_PUSH_SS(*M);
    Constant * POP_SS = Get_POP_SS(*M);
    Value * OneByte = ConstantInt::get(Int64Ty, 8, /*isSigned=*/false);


    // GotStolen Handler
    // ----------------------------------------------
    {
        // Clone detach Block 
        // Create label after the call inst. This will be the got stolen handler
        // -------------------------------------------------------------------------
        DebugInfoFinder DIFinder;      
        //ValueToValueMapTy VMap; 
        DISubprogram *SP = F->getSubprogram();
        if (SP) {
            //assert(!MustCloneSP || ModuleLevelChanges);
            // Add mappings for some DebugInfo nodes that we don't want duplicated
            // even if they're distinct.
            auto &MD = VMapGH.MD();
            MD[SP->getUnit()].reset(SP->getUnit());
            MD[SP->getType()].reset(SP->getType());
            MD[SP->getFile()].reset(SP->getFile());  
            MD[SP].reset(SP); 
        }        

    
        // Perform the actual cloning
        BasicBlock * detachBB = Detach.getDetached(); 
        BasicBlock * stolenhandler      = CloneBasicBlock(detachBB, VMapGH, ".gotstolen", F, nullptr, &DIFinder);
        VMapGH[detachBB]      = stolenhandler;        
     
        // --------------------------------------------------------------
        // Remap the cloned instruction
        for (Instruction &II : *stolenhandler) {
            RemapInstruction(&II, VMapGH, RF_IgnoreMissingLocals, nullptr, nullptr);
        }

        // Add potential jump from detachBB to got stolen handler
        IRBuilder<> builder(detachBB->getFirstNonPHIOrDbgOrLifetime()); 
        builder.CreateCall(potentialJump, {BlockAddress::get( stolenhandler )});

        for( Instruction &II : *detachBB){
          if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->getIntrinsicID() != Intrinsic::x86_uli_potential_jump){                    
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
        

        bbList.push_back(detachBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator() ))  ){
                // Don't push anymore if we encountered reattach instruction
                prevReattachInst = dyn_cast<ReattachInst>( bb->getTerminator() );
                startOfStealHandler = prevReattachInst->getDetachContinue();
                fastBuilder.SetInsertPoint( startOfStealHandler->getFirstNonPHIOrDbgOrLifetime() );
                
                // Build the Fast Path Prologue
                // push_ss((void*) (builtin_sp() - 8) );
                Value * SPVal = fastBuilder.CreateCall(getSP);
                Value * SPValInt = fastBuilder.CreateCast(Instruction::PtrToInt, SPVal, IntegerType::getInt64Ty(C));
                Value * ppRA  = fastBuilder.CreateSub(SPValInt, OneByte);
                ppRA = fastBuilder.CreateCast(Instruction::IntToPtr, ppRA, IntegerType::getInt8Ty(C)->getPointerTo());
                fastBuilder.CreateCall(PUSH_SS, {ppRA});

            } else {
                for( pred_iterator PI = pred_begin(bb); PI!=pred_end(bb); PI++ ){                
                    bbList.push_back(*PI);
                }
            }
        }
        
        // Look for the forkable function. 
        if(prevReattachInst){
            BasicBlock * prevReattachBB = prevReattachInst->getParent();
            for( Instruction &II : *prevReattachBB){
                if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->getIntrinsicID() != Intrinsic::x86_uli_potential_jump){
                    BasicBlock * stealhandler = dyn_cast<BasicBlock>(VMap[startOfStealHandler]);                    
                    // Associate callsite instruction with steal handler
                    M->CallStealMap[&II].stealHandler = stealhandler;
                    // Indicate the steal hander basic block needs a label
                    M->StealHandlerExists[stealhandler] = true;
                    
                    dyn_cast<CallInst>(&II)->getCalledFunction()->addFnAttr(Attribute::Forkable);
                    break;
                }
            }            
        }

        bbList.clear();
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
    DetachInst* detachClone = dyn_cast<DetachInst>(VMap[&Detach]);
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

        IRBuilder<> slowBuilder(detachBB->getFirstNonPHIOrDbgOrLifetime()); 
     
        using AsmPrototypeVoidStar = void* (void);
        using AsmPrototypeVoidStarStar = void** (void);
        using AsmPrototypeLong = long (void);

        Value * newrsp; // void *
        Value * otherproc; // long
        Value * addrOfRA_2; // void ** 
        Value * resumePoint; // void *
        Value * otherptr; // long

        bbList.push_back(detachBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator() ))  ){
                // Don't push anymore if we encountered reattach instruction
                prevReattachInst = dyn_cast<ReattachInst>( bb->getTerminator() );
                startOfStealHandler = prevReattachInst->getDetachContinue();
                slowBuilder.SetInsertPoint( startOfStealHandler->getFirstNonPHIOrDbgOrLifetime() );
  
                // __builtin_setup_rbp_from_sp_in_rbp();
                slowBuilder.CreateCall(setupRBPfromRSPinRBP);
                

                /*
                  Value * newrsp; // void *
                  Value * otherproc; // long
                  Value * addrOfRA_2; // void ** 
                  Value * resumePoint; // void *
                  Value * otherptr; // long
                 */
                
                FunctionType *FAsmVoidStarTy =
                    TypeBuilder<AsmPrototypeVoidStar, false>::get(C);
                FunctionType *FAsmVoidStarStarTy =
                    TypeBuilder<AsmPrototypeVoidStarStar, false>::get(C);
                FunctionType *FAsmLongTy =
                    TypeBuilder<AsmPrototypeLong, false>::get(C);

                /*
                  asm volatile("movq %%rsp, %[ARG]\n\t":[ARG] "=r" (newrsp));
                  asm volatile("movq 0(%%rsp), %[ARG]\n\t":[ARG] "=r" (otherproc));
                  asm volatile("movq -8(%%rsp), %[ARG]\n\t":[ARG] "=r" (addrOfRA_2));
                  asm volatile("movq -16(%%rsp), %[ARG]\n\t":[ARG] "=r" (resumePoint));
                  asm volatile("movq -24(%%rsp), %[ARG]\n\t":[ARG] "=r" (otherptr));
                 */

                // Get the type of routine
                Value *Asm = InlineAsm::get(FAsmVoidStarTy,
                                            "movq %rsp, $0\0A\09",
                                            "=r,~{dirflag},~{fpsr},~{flags}",
                                            /*sideeffects*/ true);
                newrsp = slowBuilder.CreateCall(Asm);

                Asm = InlineAsm::get(FAsmLongTy, 
                                     "movq 0(%rsp), $0\0A\09",
                                     "=r,~{dirflag},~{fpsr},~{flags}",
                                     /*sideeffects*/ true);

                otherproc = slowBuilder.CreateCall(Asm);

                Asm = InlineAsm::get(FAsmVoidStarStarTy, 
                                     "movq -8(%rsp), $0\0A\09",
                                     "=r,~{dirflag},~{fpsr},~{flags}",
                                     /*sideeffects*/ true);

                addrOfRA_2 = slowBuilder.CreateCall(Asm);

                Asm = InlineAsm::get(FAsmVoidStarStarTy, 
                                     "movq -16(%rsp), $0\0A\09",
                                     "=r,~{dirflag},~{fpsr},~{flags}",
                                     /*sideeffects*/ true);

                resumePoint = slowBuilder.CreateCall(Asm);

                Asm = InlineAsm::get(FAsmLongTy, 
                                     "movq -24(%rsp), $0\0A\09",
                                     "=r,~{dirflag},~{fpsr},~{flags}",
                                     /*sideeffects*/ true);
                
                otherptr = slowBuilder.CreateCall(Asm);

                
            } else {
                for( pred_iterator PI = pred_begin(bb); PI!=pred_end(bb); PI++ ){                
                    bbList.push_back(*PI);
                }
            }
        }
        
        bbList.clear();

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
                slowBuilder.SetInsertPoint(bb->getTerminator());


                //slowBuilder.CreateCall(RESUME2SCHEDULER, {addrOfRA_2, , newrsp, otherproc, otherptr, });
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


void CASABI::preProcessFunction(Function &F) {

  // Add Thread initialization and deinitialization on the main function
  // TODO : Make this optional
  if ( F.getName() == "main") {
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(F.getContext());
    
    IRBuilder<> B(F.getEntryBlock().getTerminator());
    
    for (auto &BB : F){
      Instruction * termInst = BB.getTerminator();
      if(isa<ReturnInst>(termInst)){
          B.SetInsertPoint(termInst);
      }
    }   

    return;
  } 
  
  Module *M = F.getParent();
  LLVMContext& C = M->getContext();

  Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
  IRBuilder<> builder( C );



  // Clone the function, create the slow path
  // Clone the basic block
  // -------------------------------------------------------------------------
  DebugInfoFinder DIFinder;      
  //ValueToValueMapTy VMap; 
  DISubprogram *SP = F.getSubprogram();
  if (SP) {
      //assert(!MustCloneSP || ModuleLevelChanges);
      // Add mappings for some DebugInfo nodes that we don't want duplicated
      // even if they're distinct.
      auto &MD = VMap.MD();
      MD[SP->getUnit()].reset(SP->getUnit());
      MD[SP->getType()].reset(SP->getType());
      MD[SP->getFile()].reset(SP->getFile());  
      MD[SP].reset(SP); 
  }

  // Delete the alloca in the cloned entry so that it is not used during remap
  SmallVector<Instruction *,2> delInstrs;
  
  // Collect the basic block to clone
  for( auto &BB : F){
      bbV2Clone.push_back(&BB);
  }
  
  BasicBlock * entryBB =  dyn_cast<BasicBlock>( &F.getEntryBlock());
  // Perform the actual cloning
  for (auto pBB : bbV2Clone){
      BasicBlock *bbC = CloneBasicBlock(pBB, VMap, ".clone", &F, nullptr, &DIFinder);
      VMap[pBB] = bbC;        
     
      if(pBB == entryBB){
          builder.SetInsertPoint(entryBB->getTerminator());
          builder.CreateCall(potentialJump, {BlockAddress::get(bbC)});
      }

  }
   
  // --------------------------------------------------------------
  // Remap the cloned instruction
  for (auto pBB : bbV2Clone){
      BasicBlock* bbC = dyn_cast<BasicBlock>(VMap[pBB]);
      for (Instruction &II : *bbC) {
          RemapInstruction(&II, VMap,
                           RF_IgnoreMissingLocals,
                           nullptr, nullptr);
      }
  }

  // In slow path
  // 1. Looked for alloca inst.
  // 2. Replace all uses with the original instruction
  // 3. Delete the alloca inst. 
  for (auto pBB : bbV2Clone){
      for (Instruction &II : *pBB) {
          if(isa<AllocaInst>(&II)){
              Instruction * iclone = dyn_cast<Instruction>(VMap[&II]);
              iclone->replaceAllUsesWith(&II);
              delInstrs.push_back(iclone);
          }
      }
  }
  for(auto II : delInstrs){
      II->eraseFromParent();
  }


  // -------------------------------------------------------------
  // Create the resume path
  for (auto pBB : bbV2Clone){
      if( SyncInst *SI = dyn_cast<SyncInst>(pBB->getTerminator()) ){
          Function *SetupRBPfromRSP = Intrinsic::getDeclaration(M, Intrinsic::x86_setup_rbp_from_rsp);
          Constant * DEC_SS = Get_DEC_SS(*M);
          // Resume Parent path
          {
              BasicBlock * resume_parent = BasicBlock::Create(C, "resume_parent", &F);
              IRBuilder <> B(resume_parent);
              B.CreateCall(SetupRBPfromRSP);
              B.CreateCall(DEC_SS);
              B.CreateBr(SI->getSuccessor(0));
        
              builder.SetInsertPoint(entryBB->getTerminator());
              builder.CreateCall(potentialJump, {BlockAddress::get(resume_parent)});

          }
      }
  }

  return;
}



struct AllocaInfo {
  SmallVector<BasicBlock *, 32> DefiningBlocks;
  SmallVector<BasicBlock *, 32> UsingBlocks;

  StoreInst *OnlyStore;
  BasicBlock *OnlyBlock;
  bool OnlyUsedInOneBlock;

  Value *AllocaPointerVal;
    //TinyPtrVector<DbgInfoIntrinsic *> DbgDeclares;
  
  
  void clear() {
    DefiningBlocks.clear();
    UsingBlocks.clear();
    OnlyStore = nullptr;
    OnlyBlock = nullptr;
    OnlyUsedInOneBlock = true;
    AllocaPointerVal = nullptr;
    //DbgDeclares.clear();
  }

  /// Scan the uses of the specified alloca, filling in the AllocaInfo used
  /// by the rest of the pass to reason about the uses of this alloca.
  void AnalyzeAlloca(AllocaInst *AI) {
    clear();

    //outs() << "Alloca Inst " << AI->getName() << "\n";

    // As we scan the uses of the alloca instruction, keep track of stores,
    // and decide whether all of the loads and stores to the alloca are within
    // the same basic block.
    for (auto UI = AI->user_begin(), E = AI->user_end(); UI != E;) {
      Instruction *User = cast<Instruction>(*UI++);

      if (StoreInst *SI = dyn_cast<StoreInst>(User)) {
        // Remember the basic blocks which define new values for the alloca
        DefiningBlocks.push_back(SI->getParent());
        AllocaPointerVal = SI->getOperand(0);
        OnlyStore = SI;

        //outs() << "Define block " << SI->getParent()->getName() << "\n";

      } else if (LoadInst *LI = dyn_cast<LoadInst>(User)) {
        // Otherwise it must be a load instruction, keep track of variable
        // reads.
        UsingBlocks.push_back(LI->getParent());
        AllocaPointerVal = LI;

        //outs() << "Using block " << LI->getParent()->getName() << "\n";

      } else continue;

      if (OnlyUsedInOneBlock) {
        if (!OnlyBlock)
          OnlyBlock = User->getParent();
        else if (OnlyBlock != User->getParent())
          OnlyUsedInOneBlock = false;
      }
    }

      //DbgDeclares = FindDbgAddrUses(AI);
  }

};

static void ExternComputeLiveInBlocks(
    AllocaInst *AI, AllocaInfo &Info,
    const SmallPtrSetImpl<BasicBlock *> &DefBlocks,
    SmallPtrSetImpl<BasicBlock *> &LiveInBlocks) {
  // To determine liveness, we must iterate through the predecessors of blocks
  // where the def is live.  Blocks are added to the worklist if we need to
  // check their predecessors.  Start with all the using blocks.
  SmallVector<BasicBlock *, 64> LiveInBlockWorklist(Info.UsingBlocks.begin(),
                                                    Info.UsingBlocks.end());

  // If any of the using blocks is also a definition block, check to see if the
  // definition occurs before or after the use.  If it happens before the use,
  // the value isn't really live-in.
  for (unsigned i = 0, e = LiveInBlockWorklist.size(); i != e; ++i) {
    BasicBlock *BB = LiveInBlockWorklist[i];
    if (!DefBlocks.count(BB))
      continue;

    // Okay, this is a block that both uses and defines the value.  If the first
    // reference to the alloca is a def (store), then we know it isn't live-in.
    for (BasicBlock::iterator I = BB->begin();; ++I) {
      if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
        if (SI->getOperand(1) != AI)
          continue;

        // We found a store to the alloca before a load.  The alloca is not
        // actually live-in here.
        LiveInBlockWorklist[i] = LiveInBlockWorklist.back();
        LiveInBlockWorklist.pop_back();
        --i;
        --e;
        break;
      }

      if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
        if (LI->getOperand(0) != AI)
          continue;

        // Okay, we found a load before a store to the alloca.  It is actually
        // live into this block.
        break;
      }
    }
  }

  // Now that we have a set of blocks where the phi is live-in, recursively add
  // their predecessors until we find the full region the value is live.
  while (!LiveInBlockWorklist.empty()) {
    BasicBlock *BB = LiveInBlockWorklist.pop_back_val();

    // The block really is live in here, insert it into the set.  If already in
    // the set, then it has already been processed.
    if (!LiveInBlocks.insert(BB).second)
      continue;

    // Since the value is live into BB, it is either defined in a predecessor or
    // live into it to.  Add the preds to the worklist unless they are a
    // defining block.
    for (BasicBlock *P : predecessors(BB)) {
      // The value is not live into a predecessor if it defines the value.
      if (DefBlocks.count(P))
        continue;

      // Otherwise it is, add to the worklist.
      LiveInBlockWorklist.push_back(P);
    }
  }
}

void ComputeLiveInBlocks(
    AllocaInst *AI, AllocaInfo &Info,
    const SmallPtrSetImpl<BasicBlock *> &DefBlocks,
    SmallPtrSetImpl<BasicBlock *> &LiveInBlocks) {
  ExternComputeLiveInBlocks(AI, Info, DefBlocks, LiveInBlocks);
}



void CASABI::postProcessFunction(Function &F) {
    // TODO
    // Find all alloca instruction.
    // Compute blocks that they are live in
    // Reload those live variables if they are live in a steal handler
    // lib/Transforms/Utils/PromoteMemoryToRegister.cpp ComputeLiveIn
    
    Module * M = F.getParent();

    std::vector<AllocaInst *> Allocas;
    for (auto pBB : bbV2Clone){
      for (Instruction &II : *pBB) {
          if(isa<AllocaInst>(&II)){
              Allocas.push_back(dyn_cast<AllocaInst>(&II));
          }
      }
    }

    // Map Basic block to an array of Live variables
    DenseMap<BasicBlock * , std::vector<AllocaInst *>> liveInBB;

    AllocaInfo Info;
    for(AllocaInst * AI : Allocas){
        Info.AnalyzeAlloca(AI);

        SmallPtrSet<BasicBlock *, 32> DefBlocks;
        DefBlocks.insert(Info.DefiningBlocks.begin(), Info.DefiningBlocks.end());

        // Determine which blocks the value is live in.  These are blocks which lead
        // to uses.
        SmallPtrSet<BasicBlock *, 32> LiveInBlocks;
        ComputeLiveInBlocks(AI, Info, DefBlocks, LiveInBlocks);

        for(BasicBlock * bb : LiveInBlocks){
            //outs() << "Live Blocks : " << bb->getName() << "\n";
            if (M->StealHandlerExists[bb]){
                liveInBB[bb].push_back(AI);
            }
        }
    }

    for(auto &KV :liveInBB){
        outs() << "Basic block " << KV.first->getName() << "\n";
        
        for(AllocaInst * AI : KV.second){ 
            outs() << "Alloca inst : " << AI->getName() << "\n";
        }
    }
    
    return;
}

void CASABI::postProcessHelper(Function &F) {
    //assert(false);
}

bool CASABILoopSpawning::processLoop() {
    //assert(false);
  return false;
}

CASABI::CASABI() {}

