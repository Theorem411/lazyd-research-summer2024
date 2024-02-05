#include "llvm/Transforms/ULI/ParallelRegion.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
// #include "llvm/PassSupport.h"
#include "llvm/PassRegistry.h"
// #include "llvm/IR/CallSite.h" // deprecated
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;

#define PR_NAME "parallel-region"
#define DEBUG_TYPE PR_NAME

// cl::opt<bool> UseRuntimePFor(
//     "use-runtime-pfor", cl::init(false), cl::Hidden,
//     cl::desc("Insert a call into the Parallel Loop runtime to handle cilk_for
//     loops"));
STATISTIC(NumFn, "number of functions in callgraph");
STATISTIC(
    NumDefinitelyDAC,
    "number of outlined functions that are definitely DAC outlining fashion.");
STATISTIC(NumUnsure, "number of outlined functions that are unsure of using "
                     "either DAC or EF outlining fashion.");
STATISTIC(
    NumParallelRegions,
    "number of outlined functions that were originally parallel regions.");

class ParallelRegionImpl {
public:
  ParallelRegionImpl(Module &M, CallGraph &CG) : M(M), CG(CG){};
  bool run();

private:
  bool runOnSCC(CallGraphSCC &SCC);
  bool isParallelRegion(CallGraphNode *CGN);

private:
  Module &M;
  CallGraph &CG;

  // record all callnodes that corresponds to definitely dac
  SmallSet<CallGraphNode *, 8> definitelyDACOutlineFn;
};

bool ParallelRegionImpl::isParallelRegion(CallGraphNode *CGN) {
  Function *F = CGN->getFunction();
  assert(F && "encounter callgraph node with null function");

  // TODO: for each callnode in the callgrpah, identify fn attr using
  // bool hasAttr =
  // OutlineFcn->getFnAttribute("your-custom-attribute").getValueAsString()=="true";
  return F->getFnAttribute("parallel-region").getValueAsString() == "true";
}

bool ParallelRegionImpl::run() {
  /**
   *
   */
  // worklist algorithm
  SmallVector<CallGraphNode *, 8> workList;
  SmallSet<CallGraphNode *, 8> workSet;

  for (auto &CNP : CG) {
    CallGraphNode *CGNode = CNP.second.get();
    assert(CGNode && "encounter null call graph node");
    // update statistic NumFn
    NumFn++;
    if (isParallelRegion(CGNode)) {
      // for (callee of CGNode) { put into worklist }
      for (auto &CallRecord : *CGNode) {
        if (!CallRecord.first.hasValue()) {
            // in the case of callback function, there is no callsite
            continue;
        }
        CallGraphNode *CalleeNode = CallRecord.second;
        assert(CalleeNode && "encounter null second field in CallRecord!");

        Function *Callee = CalleeNode->getFunction();
        if (!Callee)
            continue;
        workList.push_back(CGNode);
        workSet.insert(CGNode);
      }
      // increment statistic
      ++NumParallelRegions;
    }
  }
  // worklist algorithm through call graph, mark each callgraph node as DAC if
  // it has a caller that's parallel region or DAC
//   size_t i = 0; 
//   while (i < workList.size()) {
        // DEBUG: if workList.size() is constprop then not good
//   }
  for (size_t i = 0; i < workList.size(); ++i) {

    CallGraphNode *CGN = workList[i];
    assert(CGN && "worklist shouldn't have null callnode!");

    if (workSet.find(CGN) != workSet.end())
      continue;
    workSet.insert(CGN);
    if (!isParallelRegion(CGN)) {
      definitelyDACOutlineFn.insert(CGN);
      // increment definitely-DAC statistics
      NumDefinitelyDAC++;
    }

    // iterate through callees of Call Node using CallNodeRecord
    for (auto &CallRecord : *CGN) {
      if (!CallRecord.first.hasValue()) {
        // in the case of callback function, there is no callsite
        continue;
      }
      CallGraphNode *CalleeNode = CallRecord.second;
      assert(CalleeNode && "encounter null second field in CallRecord!");

      Function *Callee = CalleeNode->getFunction();
      if (!Callee)
        continue;

      if (workSet.find(CalleeNode) != workSet.end()) {
        
        workList.push_back(CalleeNode);
        workSet.insert(CalleeNode);
      }
    }
  }

  return false;
}

bool ParallelRegionImpl::runOnSCC(CallGraphSCC &SCC) { return false; }

PreservedAnalyses ParallelRegionPass::run(Module &M,
                                          ModuleAnalysisManager &AM) {
  CallGraph &CG = AM.getResult<CallGraphAnalysis>(M);
  bool Changed = ParallelRegionImpl(M, CG).run();
  if (Changed)
    return PreservedAnalyses::none();
  return PreservedAnalyses::all();
}

namespace {
struct ParallelRegion : public ModulePass {
  static char ID;

  explicit ParallelRegion() : ModulePass(ID) {
    // initializeParallelRegionPass(*PassRegistry::getPassRegistry());
  }

  bool runOnModule(Module &M) override {
    CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();

    return ParallelRegionImpl(M, CG).run();
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<CallGraphWrapperPass>();
    AU.setPreservesAll();
  }
};
} // namespace

char ParallelRegion::ID = 0;

static RegisterPass<ParallelRegion> X(PR_NAME, "false", "false");
// static const char pr_name[] = "Conduct CallGraph Analysis to determine "
//                               "outlining fashion of parallel-regions";
// INITIALIZE_PASS_BEGIN(ParallelRegion, PR_NAME, pr_name, false, false)
// INITIALIZE_PASS_DEPENDENCY(CallGraphWrapperPass)
// INITIALIZE_PASS_END(ParallelRegion, PR_NAME, pr_name, false, false)

// namespace llvm {
// Pass *createParallelRegionPass() { return new ParallelRegion(); }
// } // namespace llvm
