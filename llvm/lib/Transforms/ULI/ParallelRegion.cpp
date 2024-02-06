#include "llvm/Transforms/ULI/ParallelRegion.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/PassInfo.h"
// #include "llvm/PassSupport.h"
#include "llvm/PassRegistry.h"
// #include "llvm/IR/CallSite.h" // deprecated
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#define PR_NAME "parallel-region"
#define DEBUG_TYPE PR_NAME

using namespace llvm;

STATISTIC(NumFn, "Number of functions in callgraph");
STATISTIC(
    NumDefinitelyDAC,
    "Number of outlined functions that are definitely DAC outlining fashion.");
STATISTIC(NumUnsure, "Number of outlined functions that are unsure of using "
                     "either DAC or EF outlining fashion.");
STATISTIC(
    NumParallelRegions,
    "Number of outlined functions that were originally parallel regions.");

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
  SmallSet<CallGraphNode *, 8> parallelRegionOutlineFn;
};

bool ParallelRegionImpl::isParallelRegion(CallGraphNode *CGN) {
  Function *F = CGN->getFunction();
  //   assert(F && "encounter callgraph node with null function");

  // TODO: for each callnode in the callgrpah, identify fn attr using
  return F && F->getFnAttribute("parallel-region").getValueAsString() == "true";
}

bool ParallelRegionImpl::run() {
  // worklist algorithm
  SmallVector<CallGraphNode *, 8> workList;
  SmallSet<CallGraphNode *, 8> workSet;

  // initialize worklist with callee nodes of Parallel-region nodes
//   outs() << "CG: \n";
//   CG.dump();

  for (auto &it : CG) {
    CallGraphNode *CGNode = it.second.get();
    assert(CGNode && "encounter null call graph node");
    
    // update total function counting 
    outs() << "Function #" << NumFn;
    if (!CGNode->getFunction()) {
        outs() << ": null\n";
    } else {
        Function *Fn = CGNode->getFunction();
        outs() << ": " << Fn->getName() << "\n"; //  << Fn->getFnAttribute("parallel-region").getKindAsString() << "\n";
        ++NumFn;
    }

    if (isParallelRegion(CGNode)) {
        // DEBUG
      outs() << "Found parallel-region cgnode: " << CGNode->getFunction()->getName() << "\n";

      // increment parallel-region count
      parallelRegionOutlineFn.insert(CGNode);
      ++NumParallelRegions;
      // populate worklist with first layer of callee nodes of parallel-regions
      for (auto &CallRecord : *CGNode) {
        if (!CallRecord.first.hasValue()) {
          // in the case of callback function, there is no callsite
          continue;
        }
        CallGraphNode *CalleeNode = CallRecord.second;
        assert(CalleeNode && "encounter null second field in CallRecord!");

        Function *Callee = CalleeNode->getFunction();
        if (!Callee) //
          continue;
        workList.push_back(CGNode);
      }
    }
  }
//   outs() << "worklist after initialization";
  
  // worklist algorithm through call graph, mark each callgraph node as DAC if
  outs() << "begin propagating worklist...\n";
//   outs() << "worklist has size = " << workList.size() << "\n";
  for (size_t i = 0; i < workList.size(); ++i) {

    outs() << i << ": " << workList.size() << "\n";
    CallGraphNode *CGN = workList[i];
    assert(CGN && "worklist shouldn't have null callnode!");

    if (workSet.find(CGN) != workSet.end())
      continue;
    workSet.insert(CGN);

    // update definitely DAC count
    definitelyDACOutlineFn.insert(CGN);
    ++NumDefinitelyDAC;
   
    // put callee nodes of current back on worklist
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

      if (workSet.find(CalleeNode) == workSet.end()) {
        workList.push_back(CalleeNode);
      }
    }
  }

  // DEBUG: final printing
  outs() << "printing parallel region outline\n";
  for (CallGraphNode *CGN : parallelRegionOutlineFn) {
    Function *F = CGN->getFunction();
    assert(F && "parallelRegionOutlineFn shouldn't have null function");
    outs() << F->getName() << "\n";
  }
  outs() << "\n";

  outs() << "printing definitelyDACOutlineFn\n";
  for (CallGraphNode *CGN : definitelyDACOutlineFn) {
    Function *F = CGN->getFunction();
    assert(F && "definitelyDACOutlinFn shouldn't have null function");
    outs() << F->getName() << "\n";
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
    // llvm::initializeParallelRegionPass(*PassRegistry::getPassRegistry());
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
static RegisterPass<ParallelRegion> 
X("parallel-region", "Conduct CallGraph Analysis to determine outlining fashion of parallel-regions");

// INITIALIZE_PASS(ParallelRegion, PR_NAME, pr_name, false, false)
// static const char pr_name[] = "Conduct CallGraph Analysis to determine "
//                               "outlining fashion of parallel-regions";
// INITIALIZE_PASS_BEGIN(ParallelRegion, "ParallelRegion", pr_name, false, false)
// INITIALIZE_PASS_DEPENDENCY(CallGraphWrapperPass)
// INITIALIZE_PASS_END(ParallelRegion, "ParallelRegion", pr_name, false, false)

// namespace llvm {
// Pass *createParallelRegionPass() { return new ParallelRegion(); }
// } // namespace llvm
