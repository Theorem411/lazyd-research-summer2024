#ifndef LLVM_ANALYSIS_REACHINGDETACHINST_H
#define LLVM_ANALYSIS_REACHINGDETACHINST_H


#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"

#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/ADT/BitVector.h"

//#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"


//using namespace llvm;
//using namespace std;

namespace llvm {

class ReachingDetachInst  {
 public:
  using MapDetachToBBTy = DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>;
  using MapSyncToBBTy = DenseMap<SyncInst *, SmallPtrSet<BasicBlock*, 8>>;

  ReachingDetachInst() {};
  //explicit ReachingDetachInst(Function &F) { recalculate(F); }

  void recalculate(Function& F, FunctionAnalysisManager &AM, DominatorTree &DT, LoopInfo &LI);

  // Stores the path that starts from a detach to another detach inst (the key)
  // Key   = DetachInst
  // Value = Path that starts from a detach and reaches that key
  MapDetachToBBTy &getReachingDetachPathMap();

  MapSyncToBBTy &getReachingSyncPathMap();

  // Stores the detach's parent that reaches this detach inst (the key)
  // Key   = DetachInst
  // Value = Detach's parent that reaches this detach inst (the key)
  MapDetachToBBTy &getReachingDetachBBMap();

  SmallVector<BasicBlock*, 4>  &getSeqOrder() ;
  SmallVector<BasicBlock*, 4>  &getLoopOrder() ;

  DenseMap<BasicBlock*, BitVector> &getMapBB2InVal();

  SmallVector<DetachInst*, 4>  &getSeqOrderInst() ;
  SmallVector<DetachInst*, 4>  &getLoopOrderInst() ;


  static void registerClangPass(const PassManagerBuilder &, legacy::PassManagerBase &PM);
 private:
  // Stores the path that starts from a detach to another detach inst (the key)
  // Key   = DetachInst
  // Value = Path that starts from a detach and reaches that key
  MapDetachToBBTy MapDetachToPath;

  MapSyncToBBTy MapSyncToPath;

  // Stores the detach's parent that reaches this detach inst (the key)
  // Key   = DetachInst
  // Value = Detach's parent that reaches this detach inst (the key)
  MapDetachToBBTy MapDetachToReachDetach;

  SmallVector<BasicBlock*, 4> bbTraverse;
  DenseMap<BasicBlock*, int> mapBB2idx;
  SmallVector<DetachInst*, 4> detachList;
  SmallVector<SyncInst*, 4> syncList;

  DenseMap<BasicBlock*, BitVector> mapBB2InVal;
  DenseMap<BasicBlock*, BitVector> mapBB2OutVal;

  // Ignore back edge loop
  DenseMap<BasicBlock*, BitVector> mapBB2InValLoop;
  DenseMap<BasicBlock*, BitVector> mapBB2OutValLoop;

  SmallVector<BasicBlock*, 4> bbSeqOrder;
  SmallVector<BasicBlock*, 4> bbLoopOrder;

  SmallVector<DetachInst*, 4> bbSeqOrderInst;
  SmallVector<DetachInst*, 4> bbLoopOrderInst;


  BitVector unionFcn (std::vector<BitVector> &values);
  unsigned createWorkList(BasicBlock * entry);
  void createOrderOfDetach( LoopInfo &LI, BitVector& initBB ) ;
  void orderDetach(SmallVector<BasicBlock*, 4>& normalCfgBB, DenseMap<BasicBlock*, BitVector>& mapBB2Val, SmallVector<BasicBlock*, 4>& bbOrder, SmallVector<DetachInst*, 4>& bbOrderInst);
  void runFlowWithoutLoop( DominatorTree &DT,  BasicBlock * entry, BitVector& initBound  ) ;
  void runFlow(  BasicBlock * entry, BitVector& initBound  );

  // Return true if src can reach dst, otherwise false
  bool isReaching(BasicBlock * src, BasicBlock * dst);

};

#if 0

 class ReachingDetachInstAnalysis : public AnalysisInfoMixin<ReachingDetachInstAnalysis> {
   friend AnalysisInfoMixin<ReachingDetachInstAnalysis>;
   static AnalysisKey Key;

public:
   /// \brief Provide the result typedef for this analysis pass.
   using Result = ReachingDetachInst;

   /// \brief Run the analysis pass over a function and produce a dominator tree.
   ReachingDetachInst run(Function &F, FunctionAnalysisManager &);

 };

class ReachingDetachInstWrapperPass : public FunctionPass {
 public:
  static char ID;

  ReachingDetachInstWrapperPass() : FunctionPass(ID) {
    outs() << "RDI Initialize 1\n";
    initializeReachingDetachInstWrapperPassPass(*PassRegistry::getPassRegistry());
    outs() << "RDI Initialize 2\n";
  }

  ReachingDetachInst &getReachingDetachInst() { return RDI; }
  const ReachingDetachInst &getReachingDetachInst() const { return RDI; }


  bool runOnFunction(Function& F) override;
  void getAnalysisUsage(AnalysisUsage& AU) const;

  //static void registerClangPass(const PassManagerBuilder &, legacy::PassManagerBase &PM);
 private:
  ReachingDetachInst RDI;
};


 Pass *createReachingDetachInstWrapperPassPass();

#endif

}

#endif
