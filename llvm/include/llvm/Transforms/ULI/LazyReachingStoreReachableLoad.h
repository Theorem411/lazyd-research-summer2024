#ifndef LLVM_ANALYSIS_REACHINGSTOREREACHABLELOAD_H
#define LLVM_ANALYSIS_REACHINGSTOREREACHABLELOAD_H


#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"

#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/ADT/BitVector.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"


//using namespace llvm;

namespace llvm {

class ReachingStoreReachableLoad  {
 public:
  
  ReachingStoreReachableLoad() {};

  void recalculate(Function& F, FunctionAnalysisManager &AM, DominatorTree &DT, LoopInfo &LI);
  
  DenseMap<BasicBlock*, SmallPtrSet<Instruction*, 8>>& getReachingStore() {
    return MapBB2ReachingAlloca;
  } 

 private:
  SmallVector<BasicBlock*, 4> bbTraverse;

  // Reaching Alloca
  DenseMap<Instruction*, unsigned> mapStr2IdxReachingAlloca;
  SmallVector<Instruction*, 4> mapIdx2StrReachingAlloca;
  
  DenseMap<BasicBlock*, BitVector> mapBB2InValReachingAlloca;
  DenseMap<BasicBlock*, BitVector> mapBB2OutValReachingAlloca;  
  
  DenseMap<BasicBlock*, SmallPtrSet<Instruction*, 8>> MapBB2ReachingAlloca;

  // Reaching Alloca
  BitVector unionFcnReachingAlloca (std::vector<BitVector> &values);
  unsigned createWorkListReachingAlloca(BasicBlock * entry);
  void runFlowReachingAlloca(  BasicBlock * entry, BitVector& initBound  ); 
  
  // Reaching Store
  DenseMap<Instruction*, DenseMap<Instruction*, unsigned>> mapVal2IdxReachingStore;
  DenseMap<Instruction*, SmallVector<Instruction*, 4>> mapIdx2ValReachingStore;

  DenseMap<BasicBlock*, std::vector<BitVector>> mapBB2InValReachingStore;
  DenseMap<BasicBlock*, std::vector<BitVector>> mapBB2OutValReachingStore;  
  
  SmallVector<unsigned, 4> createWorkListReachingStore(BasicBlock * entry, unsigned nStrPtr);
  void runFlowReachingStore(BasicBlock * entry, SmallVector<unsigned, 4>& idxVal);
  std::vector<BitVector> unionFcnReachingStore (std::vector<std::vector<BitVector>> &values, unsigned nStrPtr);

  // Return true if src can reach dst, otherwise false
  bool isReaching(BasicBlock * src, BasicBlock * dst);
};

#if 0

 class ReachingStoreReachableLoadAnalysis : public AnalysisInfoMixin<ReachingStoreReachableLoadAnalysis> {
   friend AnalysisInfoMixin<ReachingStoreReachableLoadAnalysis>;
   static AnalysisKey Key;

public:
   /// \brief Provide the result typedef for this analysis pass.
   using Result = ReachingStoreReachableLoad;

   /// \brief Run the analysis pass over a function and produce a dominator tree.
   ReachingStoreReachableLoad run(Function &F, FunctionAnalysisManager &);

 };
 
class ReachingStoreReachableLoadWrapperPass : public FunctionPass {
 public:
  static char ID;  

  ReachingStoreReachableLoadWrapperPass() : FunctionPass(ID) { 
    outs() << "RSI Initialize 1\n";
    initializeReachingStoreReachableLoadWrapperPassPass(*PassRegistry::getPassRegistry());
    outs() << "RSI Initialize 1\n";
  }

  ReachingStoreReachableLoad &getReachingStoreReachableLoad() { return RSI; }
  const ReachingStoreReachableLoad &getReachingStoreReachableLoad() const { return RSI; }


  bool runOnFunction(Function& F) override;
  void getAnalysisUsage(AnalysisUsage& AU) const;

  //static void registerClangPass(const PassManagerBuilder &, legacy::PassManagerBase &PM);   
 private:
  ReachingStoreReachableLoad RSI;
};

 Pass *createReachingStoreReachableLoadWrapperPassPass();

#endif

}
#endif
