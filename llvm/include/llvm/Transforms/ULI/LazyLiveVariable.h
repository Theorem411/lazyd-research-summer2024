#ifndef LLVM_ANALYSIS_LIVEVARIABLE_H
#define LLVM_ANALYSIS_LIVEVARIABLE_H


#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/PassRegistry.h"

//#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"


namespace llvm {

class LiveVariable  {
public:
  using LivenessInMapTy = DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>;
  using LivenessOutMapTy = DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>;

  LiveVariable() {LivenessInMap.clear(); LivenessOutMap.clear();};
  //explicit LiveVariable(Function &F) { recalculate(F); }

  LivenessInMapTy &getLiveInInstBBMap() ;
  LivenessOutMapTy &getLiveOutInstBBMap() ;

  void recalculate(Function& F);
private:
  
  bool ignoreInst(Instruction* I);
  BitVector unionFcn (std::vector<BitVector> &values);
  BitVector livenessTrans(BitVector &value, std::vector<BitVector> &genAndKill);
  std::vector<BitVector>  instGenAndKill(BitVector &value,  Instruction* I,   ValueMap<Instruction*, unsigned> &inst2idxMap);

  LivenessInMapTy LivenessInMap;
  LivenessOutMapTy LivenessOutMap;

};


#if 0

/// \brief Analysis pass which computes a \c DominatorTree.
class LiveVariableAnalysis : public AnalysisInfoMixin<LiveVariableAnalysis> {
  friend AnalysisInfoMixin<LiveVariableAnalysis>;
  static AnalysisKey Key;

public:
  /// \brief Provide the result typedef for this analysis pass.
  using Result = LiveVariable;

  /// \brief Run the analysis pass over a function and produce a dominator tree.
  LiveVariable run(Function &F, FunctionAnalysisManager &);
};


class LiveVariableWrapperPass : public FunctionPass {
 public:
  static char ID;  

  LiveVariableWrapperPass() : FunctionPass(ID) { 
    outs() << "Live Initialize 1\n";
    initializeLiveVariableWrapperPassPass(*PassRegistry::getPassRegistry());
    outs() << "Live Initialize 2\n";
  }

  LiveVariable &getLiveVariable() { return LV; }
  const LiveVariable &getLiveVariable() const { return LV; }


  bool runOnFunction(Function& F) override;
  void getAnalysisUsage(AnalysisUsage& AU) const;

  //static void registerClangPass(const PassManagerBuilder &, legacy::PassManagerBase &PM); 
  
 private:
  LiveVariable LV;
};

 Pass *createLiveVariableWrapperPassPass();

#endif

}

#endif
