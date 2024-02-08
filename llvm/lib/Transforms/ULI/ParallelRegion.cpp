#include "llvm/Transforms/ULI/ParallelRegion.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/TapirTaskInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/PassInfo.h"
#include "llvm/PassRegistry.h"
// #include "llvm/IR/AbstractCallSite.h"
// #include "llvm/IR/CallSite.h" // deprecated
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Support/raw_ostream.h"

#define PR_NAME "parallel-region"
#define DEBUG_TYPE PR_NAME

using namespace llvm;

STATISTIC(NumFn, "Number of functions in module");
STATISTIC(NumDefinitelyDAC,
          "Number of functions that are definitely called within a parallel "
          "region, and thus must adopt DAC as its outline strategy.");
STATISTIC(NumDefinitelyEF,
          "Number of functions that are definitely called within a serial "
          "region, and thus can adopt EF as its outline strategy.");
STATISTIC(NumBoth, "Number of functions that are witnessed to be called in "
                   "both parallel and serial region, and thus must use a "
                   "global counter to decide its outline stategy.");
STATISTIC(
    NumUntouched,
    "Number of functions untouched by the end of this call-graph analysis,"
    " usually root function in the callgraph.");

class ParallelRegionImpl {
public:
  enum class FnState {
    // trivial state for initialization and for root functions
    Untouched,
    // for function whose callsites are reachable only within parallel region
    DefinitelyDAC,
    // for function whose callsites are reachable only within serial region
    DefinitelyEF,
    // for function which have evidence of both DefiniteDAC and DefinitelyEF
    Both
    // for function whose address has been taken
    // External
  };

  ParallelRegionImpl(Module &M, CallGraph &CG, DominatorTree &DT, TaskInfo &TI)
      : M(M), CG(CG), DT(DT), TI(TI){};
  bool run();

private:
  //   bool isParallelRegion(CallGraphNode *CGN); // no longer needed
  FnState joinState(Fnstate s1, FnState s2) {
    switch (s1) {
    case FnState::Both: {
      return s1;
    }
    case FnState::Untouched: {
      return s2;
    }
    case FnState::DefinitelyDAC: {
      switch
        s2 {
        case FnState::DefinitelyDAC: {
          return s2;
        }
        default: {
          return FnState::Both;
        }
        }
    }
    case FnState::DefinitelyEF: {
      switch
        s2 {
        case FnState::DefinitelyEF: {
          return s2;
        }
        default: {
          return FnState::Both;
        }
        }
    }
    }
  }

  FnState getState(Function *F) {
    assert(GlobalFnStates.find(F) != GlobalFnStates.end() &&
           "GlobalFnStates doesn't contain function when getState is called!");
    return GlobalFnStates[F];
  }

  void updateState(Function *F, FnState stateNew) {
    assert(GlobalFnStates.find(F) != GlobalFnStates.end() &&
           "F is not registered in GlobalFnStates!");
    FnState stateOld = GlobalFnStates[F];
    GlobalFnStates[F] = joinState(stateOld, stateNew);
  }

  void initializeGlobalFnStates() {
    LLVM_DEBUG(dbgs() << "calling initializeGlobalFnStates...\n");

    for (auto &it : CG) {
      const Function *F = it.first;
      if (!F)
        continue;
      GlobalFnStates.insert(F, FnState::Untouched);
      // update global satistic: NumFn
      ++NumFn;

      LLVM_DEBUG(dbgs() << "Function " << F->getName()
                        << " state initialized!\n");
    }
    LLVM_DEBUG(dbgs() << "\n\n");
  }

  void initializeWorkList(SmallVector<CallGraphNode *, 8> &workList) {
    LLVM_DEBUG(dbgs() << "calling initializeWorkList...\n");
    for (auto &it : CG) {
      const Function *F = it.first;
      CallGraphNode *CGN = it.second.get();
      assert(CGN && "encounter null call graph node");
      if (!F)
        continue;
      workList.push_back(CGN);

      LLVM_DEBUG(dbgs() << "Function " << F->getName()
                        << " pushed onto workList!\n");
    }
    LLVM_DEBUG(dbgs() << "\n\n");
  }

  void printStatistic();

  // @debug
  unsigned getLine(CallBase *cs) {
    return cs->getDebugLoc().getLine();
  } 

private:
  Module &M;
  CallGraph &CG;
  DominatorTree &DT;
  TaskInfo &TI;

  // record all callnodes that corresponds to definitely dac
  //   SmallSet<CallGraphNode *, 8> definitelyDACOutlineFn;
  //   SmallSet<CallGraphNode *, 8> parallelRegionOutlineFn;
  DenseMap<Function *, FnState> GlobalFnStates;
};

// bool ParallelRegionImpl::isParallelRegion(CallGraphNode *CGN) {
//   Function *F = CGN->getFunction();
//   //   assert(F && "encounter callgraph node with null function");
//   // TODO: for each callnode in the callgrpah, identify fn attr using
//   return F && F->getFnAttribute("parallel-region").getValueAsString() ==
//   "true";
// }
void ParallelRegionImpl::printStatistic() {
  for (auto it : GlobalFnStates) {
    switch
      it.second {
      case FnState::DefinitelyDAC: {
        ++NumDefinitelyDAC;
      }
      case FnState::DefinitelyEF: {
        ++NumDefinitelyEF;
      }
      case FnState::Both: {
        ++NumBoth;
      }
      case FnState::Untouched: {
        ++NumUntouched;
      }
      }
  }
}

bool ParallelRegionImpl::run() {
  // initialize GlobalFnStates to all Untouched
  initializeGlobalFnStates();

  // initialize worklist
  SmallVector<CallGraphNode *, 8> workList;
  initializeWorkList(workList);

  // while worklist non-empty,
  //   populate
  for (size_t i = 0; i < workList.size(); ++i) {
    CallGraphNode *CGN = workList[i];
    assert(CGN && "worklist shouldn't have null callnode!");

    Function *Caller = CGN->getFunction();

    LLVM_DEBUG(dbgs() << "pop CallNode " << Caller->getname() << "...\n");

    // for each callgraph node, traverse through each of its callsite
    for (auto &CallRecord : *CGN) {
      // in the case of callback function, there is no callsite
      if (!CallRecord.first.hasValue()) {
        continue;
      }
      // if call node has explicit callsite
      assert(CallRecord.second && "encounter null second field in CallRecord!");
      Function *Callee = CallRecord.second->getFunction();
      assert(Callee && "CallRecord contains null callee node!");
      CallBase *CallSite = dyn_cast<CallBase>(CallRecord.first->get());
      assert(CallSite &&
             "CallRecord doesn't have CallBase callsite instruction!");

      LLVM_DEBUG(dbgs() << "  examing callsite at ln: << " << getLine(CallSite));
      CallSite->dump();
      LLVM_DEBUG(dbgs() << "\n");
      
      // check if callsite is in a parallel-region
      Task *T = TI[CallSite->getParent()];
      if (!T) {
        if (!Caller) {
          errs() << "Callsite "
                 << "null"
                 << "->" << Callee->getname() << " has null task!\n";
        } else {
          errs() << "Callsite " << Caller->getName() << "->"
                 << Callee->getname() << " has null task!\n";
        }
      }
      assert(T && "Callsite contains null task. There should be a root task!");

      // update state of callee node based on caller & parallel-region info
      FnState sOld = getState(Callee);
      if (T->isSerial()) {
        // callsite is in a serial region
        updateState(Callee, getState(Caller));
        updateState(Callee, FnState::DefinitelyEF);
      } else {
        // callsite is in a parallel region
        updateState(Callee, FnState::DefinitelyDAC);
      }
      FnState sNew = getState(Callee);

      // push Callee back on to worklist because of state change
      if (sOld != sNew) {
        workList.push_back(CallRecord.second);
      }
    }
  }

  //   // worklist algorithm
  //   SmallVector<CallGraphNode *, 8> workList;
  //   SmallSet<CallGraphNode *, 8> workSet;

  //   // initialize worklist with callee nodes of Parallel-region nodes
  //   for (auto &it : CG) {
  //     CallGraphNode *CGNode = it.second.get();
  //     assert(CGNode && "encounter null call graph node");

  //     // update total function counting
  //     outs() << "Function #" << NumFn;
  //     if (!CGNode->getFunction()) {
  //       outs() << ": null\n";
  //     } else {
  //       Function *Fn = CGNode->getFunction();
  //       outs() << ": " << Fn->getName() << "\n"; //  <<
  //                                                //
  //                                                Fn->getFnAttribute("parallel-region").getKindAsString()
  //                                                //  << "\n";
  //       ++NumFn;
  //     }

  //     if (isParallelRegion(CGNode)) {
  //       // increment parallel-region count
  //       parallelRegionOutlineFn.insert(CGNode);
  //       ++NumParallelRegions;
  //       // populate worklist with first layer of callee nodes of
  //       parallel-regions for (auto &CallRecord : *CGNode) {
  //         if (!CallRecord.first.hasValue()) {
  //           // in the case of callback function, there is no callsite
  //           continue;
  //         }
  //         CallGraphNode *CalleeNode = CallRecord.second;
  //         assert(CalleeNode && "encounter null second field in CallRecord!");

  //         Function *Callee = CalleeNode->getFunction();
  //         if (!Callee) //
  //           continue;
  //         workList.push_back(CGNode);
  //       }
  //     }
  //   }

  //   // worklist algorithm through call graph, mark each callgraph node as DAC
  //   if outs() << "begin propagating worklist...\n";
  //   //   outs() << "worklist has size = " << workList.size() << "\n";
  //   for (size_t i = 0; i < workList.size(); ++i) {

  //     outs() << i << ": " << workList.size() << "\n";
  //     CallGraphNode *CGN = workList[i];
  //     assert(CGN && "worklist shouldn't have null callnode!");

  //     // put callee nodes of current back on worklist
  //     for (auto &CallRecord : *CGN) {
  //       if (!CallRecord.first.hasValue()) {
  //         // in the case of callback function, there is no callsite
  //         continue;
  //       }
  //       CallGraphNode *CalleeNode = CallRecord.second;
  //       assert(CalleeNode && "encounter null second field in CallRecord!");

  //       Function *Callee = CalleeNode->getFunction();
  //       if (!Callee)
  //         continue;

  //       if (workSet.find(CalleeNode) == workSet.end()) {
  //         workList.push_back(CalleeNode);
  //       }
  //     }
  //   }

  // DEBUG: final printing
  //   outs() << "printing parallel region outline\n";
  //   for (CallGraphNode *CGN : parallelRegionOutlineFn) {
  //     Function *F = CGN->getFunction();
  //     assert(F && "parallelRegionOutlineFn shouldn't have null function");
  //     outs() << F->getName() << "\n";
  //   }
  //   outs() << "\n";

  //   outs() << "printing definitelyDACOutlineFn\n";
  //   for (CallGraphNode *CGN : definitelyDACOutlineFn) {
  //     Function *F = CGN->getFunction();
  //     assert(F && "definitelyDACOutlinFn shouldn't have null function");
  //     outs() << F->getName() << "\n";
  //   }

  // set statistics
  printStatistic();
  return false;
}

PreservedAnalyses ParallelRegionPass::run(Module &M,
                                          ModuleAnalysisManager &AM) {
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  CallGraph &CG = AM.getResult<CallGraphAnalysis>(M);
  TaskInfo &TI = AM.getResult<TaskAnalysis>(F);
  bool Changed = ParallelRegionImpl(M, CG, DT, TI).run();
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
    DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    TaskInfo &TI = getAnalysis<TaskInfoWrapperPass>().getTaskInfo();
    CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();

    return ParallelRegionImpl(M, CG, DT, TI).run();
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<CallGraphWrapperPass>();
    AU.setPreservesAll();
  }
};
} // namespace

char ParallelRegion::ID = 0;
static RegisterPass<ParallelRegion> X("parallel-region",
                                      "Conduct CallGraph Analysis to determine "
                                      "outlining fashion of parallel-regions");

// INITIALIZE_PASS(ParallelRegion, PR_NAME, pr_name, false, false)
// static const char pr_name[] = "Conduct CallGraph Analysis to determine "
//                               "outlining fashion of parallel-regions";
// INITIALIZE_PASS_BEGIN(ParallelRegion, "ParallelRegion", pr_name, false,
// false) INITIALIZE_PASS_DEPENDENCY(CallGraphWrapperPass)
// INITIALIZE_PASS_END(ParallelRegion, "ParallelRegion", pr_name, false, false)

// namespace llvm {
// Pass *createParallelRegionPass() { return new ParallelRegion(); }
// } // namespace llvm
