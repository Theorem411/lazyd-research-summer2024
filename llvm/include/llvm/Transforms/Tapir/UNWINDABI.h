//===- UNWINDABI.h - Interface to the UNWIND PRSC runtime ----*- C++ -*--===//
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
#ifndef UNWIND_ABI_H_
#define UNWIND_ABI_H_

#include "llvm/Transforms/Tapir/LoopSpawning.h"
#include "llvm/Transforms/Tapir/LoweringUtils.h"
#include "llvm/IR/IRBuilder.h"

namespace llvm {
  class Value;

  class UNWINDABILoopSpawning : public LoopOutline {
  public:
    UNWINDABILoopSpawning(Loop *OrigLoop, unsigned Grainsize, ScalarEvolution &SE,
			  LoopInfo *LI, DominatorTree *DT, AssumptionCache *AC,
			  OptimizationRemarkEmitter &ORE)
      : LoopOutline(OrigLoop, SE, LI, DT, AC, ORE)
    {}
    bool processLoop();
    virtual ~UNWINDABILoopSpawning() {}

  protected:
  };

  class UNWINDABI : public TapirTarget {
  public:
    UNWINDABI();
    Value *lowerGrainsizeCall(CallInst *GrainsizeCall) override final;

    void createSync(SyncInst &inst, ValueToValueMapTy &DetachCtxToStackFrame) ;
  
    /// @brief Create the gotstolen path 
    Function *createDetach(DetachInst &Detach,
			   ValueToValueMapTy &DetachCtxToStackFrame,
			   DominatorTree &DT, AssumptionCache &AC,  SyncInst * detachSyncPair = nullptr)  ;

    /// @brief Create the unwind block here, the prologue to slow path, the epilogue of slow path
    /// the restore entry
    void preProcessFunction(Function &F) override final;
    void postProcessFunction(Function &F) override final;
    void postProcessHelper(Function &F) override final;

    struct Sync {};
    struct Work {};
    struct PRSC_Desc {};
    struct Seed {};

    bool isULIorCAS() const override {
      return true;
    }
 
  

  private:
    void createSlowPathEpilogue(Function& F, Instruction* SI, Value* workCtx, BasicBlock* restorePath);
    //void createSlowPathEpilogue(Function& F, Value* workCtx);
    Value* createSlowPathPrologue(Function& F);
    void instrumentMainFcn(Function& F);
    void instrumentSpawningFcn(Function& F);
    void createUnwindHandler(Function& F);
    void createRestorePath(Function& F, SyncInst * SI);
    void createFastPath(DetachInst& Detach);     
    BasicBlock * createGotStolenHandler(DetachInst& Detach, SyncInst * detachSyncPair);
    void createJumpTableInit(DetachInst& Detach, BasicBlock * GotstolenHandler);
    void createJumpTable(DetachInst& Detach, BasicBlock * Continuation);
    BasicBlock * createSlowPathFcn(DetachInst& Detach);   
    bool isContinuationTre(Function &F);
    void findLiveInstAfterSync(DominatorTree &DT, DetachInst &Detach, SyncInst* Sync);
    void findLiveInstAfterCont(DominatorTree &DT, DetachInst &Detach, SyncInst* Sync);
    bool reachFromBB2Inst(BasicBlock * src, BasicBlock * dst, BasicBlock * skip = nullptr);
    void changeUseAfterPhi(Instruction* II, PHINode* phiNode, BasicBlock* BB, BasicBlock * skip = nullptr);
    void renameUseToPhi(PHINode* phiNode, Instruction* def, SyncInst* si);
    void renameUseToPhiInFrontier(PHINode* phiNode, Instruction* def, BasicBlock* phiNodeBB,
				  SmallVector< Use*, 4 >& useNeed2Update,  
				  DenseMap <Use*, PHINode*>& mapUseToPhi, 
				  SmallVector< PHINode*, 4 >&  phiNeed2Update,
				  DenseMap <PHINode*, std::vector<unsigned>> mapPhiToVIncome,
				  DenseMap <PHINode*, std::vector<PHINode*>> mapPhiToVPhi);
    bool isTre;
  };

}  // end of llvm namespace

#endif
