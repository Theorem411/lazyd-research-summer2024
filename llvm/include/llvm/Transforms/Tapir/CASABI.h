//===- CASABI.h - Interface to the CAS PRSC runtime ----*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the CAS ABI to convert Tapir instructions to calls
// into the CAS PRSC library.
//
//===----------------------------------------------------------------------===//
#ifndef CAS_ABI_H_
#define CAS_ABI_H_

#include "llvm/Transforms/Tapir/LoopSpawning.h"
#include "llvm/Transforms/Tapir/LoweringUtils.h"
#include "llvm/IR/IRBuilder.h"

namespace llvm {
class Value;

class CASABILoopSpawning : public LoopOutline {
public:
  CASABILoopSpawning(Loop *OrigLoop, unsigned Grainsize, ScalarEvolution &SE,
                      LoopInfo *LI, DominatorTree *DT, AssumptionCache *AC,
                      OptimizationRemarkEmitter &ORE)
      : LoopOutline(OrigLoop, SE, LI, DT, AC, ORE)
        // SpecifiedGrainsize(Grainsize)
  {}

  bool processLoop();

  virtual ~CASABILoopSpawning() {}

protected:
  // PHINode* canonicalizeIVs(Type *Ty);
  // Value *canonicalizeLoopLatch(PHINode *IV, Value *Limit);

  // unsigned SpecifiedGrainsize;
// private:
//   /// Report an analysis message to assist the user in diagnosing loops that are
//   /// not transformed.  These are handled as LoopAccessReport rather than
//   /// VectorizationReport because the << operator of LoopSpawningReport returns
//   /// LoopAccessReport.
//   void emitAnalysis(const LoopAccessReport &Message) const {
//     emitAnalysisDiag(OrigLoop, *ORE, Message);
//   }
};

class CASABI : public TapirTarget {
public:
  CASABI();
  Value *lowerGrainsizeCall(CallInst *GrainsizeCall) override final;
  void createSync(SyncInst &inst, ValueToValueMapTy &DetachCtxToStackFrame);

  Function *createDetach(DetachInst &Detach,
                         ValueToValueMapTy &DetachCtxToStackFrame,
                         DominatorTree &DT, AssumptionCache &AC, SyncInst * detachSyncPair = nullptr) ;
  void preProcessFunction(Function &F) override final;
  void postProcessFunction(Function &F) override final;
  void postProcessHelper(Function &F) override final;

  bool isULIorCAS() const override {
    return true;
  }


  struct Sync {};
  struct Work {};
  struct PRSC_Desc {};
  struct Seed {};


private:
    void BuildSuspendAndStealRoutine (/*input*/CallInst * callInst, Value * returnFromSteal, Value* returnFromSuspend, Function *F, Module *M, LLVMContext & C, /*ouput*/SmallVector<BasicBlock*, 2> &newBB, SmallVector<Instruction*, 2> &delInstrs);
    
    void StoreArgIntoWork(LLVMContext &C, IRBuilder<> & B, Value * Arg, int offset, Value * potentialWork, int nargc);
    void DecrementJoinCounter(IRBuilder <> & gotStolen, Module * M, LLVMContext & C);
    void SetJoinCounter(IRBuilder <> & B, int val, Module * M, LLVMContext & C);
    Value* CheckIfJoinCounterZero(IRBuilder <> & gotStolenB, Module * M, LLVMContext & C);
    void StoreFuncRes(IRBuilder <> & gotStolenB, int detachLevel, LLVMContext & C);
    void StoreRetInInlet(IRBuilder <> &B, Argument & Result, Argument & WorkPtr, Type * retType, LLVMContext & C, const DataLayout &DL);
    void PopulateAfterCheckCnt(IRBuilder <> & gotStolenB, BasicBlock * parentBB, Value * checkCntRes, DetachInst &Detach, Function * F, Module * M, LLVMContext & C);
    void GenerateInletEntry(IRBuilder<> & B, Argument & Result, Argument & WorkPtr, Type * retType, Function * Inlet, Module * M, LLVMContext & C, const DataLayout &DL);
    
    Function * GenerateWrapperFunc(Function & callFunc, Module * M, LLVMContext & C);
    Function * GenerateRemoteInlet(Function & callFunc, Module * M, LLVMContext & C);
    Function * GenerateLocalInlet(Function & callFunc, Module * M, LLVMContext & C);
    Function * GenerateHereIsWorkHandlerFunc(Function & callFunc, Module * M, LLVMContext & C);
};

}  // end of llvm namespace

#endif
