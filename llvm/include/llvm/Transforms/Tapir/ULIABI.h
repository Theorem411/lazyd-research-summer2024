//===- ULIABI.h - Interface to the ULI PRSC runtime ----*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the ULI ABI to convert Tapir instructions to calls
// into the user-level-interrupts PRSC library.
//
//===----------------------------------------------------------------------===//
#ifndef ULI_ABI_H_
#define ULI_ABI_H_

#include "llvm/Transforms/Tapir/LoopSpawning.h"
#include "llvm/Transforms/Tapir/LoweringUtils.h"

namespace llvm {
class Value;

class ULIABILoopSpawning : public LoopOutline {
public:
  ULIABILoopSpawning(Loop *OrigLoop, unsigned Grainsize, ScalarEvolution &SE,
                      LoopInfo *LI, DominatorTree *DT, AssumptionCache *AC,
                      OptimizationRemarkEmitter &ORE)
      : LoopOutline(OrigLoop, SE, LI, DT, AC, ORE)
        // SpecifiedGrainsize(Grainsize)
  {}

  bool processLoop();

  virtual ~ULIABILoopSpawning() {}

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

class ULIABI : public TapirTarget {
public:
  ULIABI();
  Value *lowerGrainsizeCall(CallInst *GrainsizeCall) override final;
  void createSync(SyncInst &inst, ValueToValueMapTy &DetachCtxToStackFrame)
    override final;

  Function *createDetach(DetachInst &Detach,
                         ValueToValueMapTy &DetachCtxToStackFrame,
                         DominatorTree &DT, AssumptionCache &AC) override final;
  void preProcessFunction(Function &F) override final;
  void postProcessFunction(Function &F) override final;
  void postProcessHelper(Function &F) override final;

  struct Sync {};
  struct Work {};
  struct PRSC_Desc {};
};

}  // end of llvm namespace

#endif
