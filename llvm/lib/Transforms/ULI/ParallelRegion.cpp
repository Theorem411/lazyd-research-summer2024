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

#define PR_NAME "parallel-region-reachable"
#define DEBUG_TYPE PR_NAME

using namespace llvm;

STATISTIC(NumFn,            "NumFn              Number of functions in module");
STATISTIC(NumDefinitelyDAC, "NumDefinitelyDAC   "
          "Number of functions that are definitely called within a parallel "
          "region, and thus must adopt DAC as its outline strategy.");
STATISTIC(NumDefinitelyEF,  "NumDefinitelyEF    "
          "Number of functions that are definitely called within a serial "
          "region, and thus can adopt EF as its outline strategy.");
STATISTIC(NumBoth,          "NumBoth            "   
                   "Number of functions that are witnessed to be called in "
                   "both parallel and serial region, and thus must use a "
                   "global counter to decide its outline stategy.");
STATISTIC(
    NumUntouched,           "NumUntouched       "
    "Number of functions untouched by the end of this call-graph analysis,"
    " usually root function in the callgraph.");
STATISTIC(NumCallback,      "NumCallback        number of callback functions");

// DEBUG: Note on how to check the function attribute defined in LoopSpawningTI
//   Function *F = CGN->getFunction();
//   //   assert(F && "encounter callgraph node with null function");
//   // TODO: for each callnode in the callgrpah, identify fn attr using
//   return F && F->getFnAttribute("parallel-region").getValueAsString() ==
//   "true";

// PreservedAnalyses ParallelRegionPass::run(Module &M,
//                                           ModuleAnalysisManager &AM) {
// // auto &FAM = AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
// //   DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(M);
//   CallGraph &CG = AM.getResult<CallGraphAnalysis>(M);
//   bool Changed = ParallelRegionImpl(M, CG, TI).run();
//   if (Changed)
//     return PreservedAnalyses::none();
//   return PreservedAnalyses::all();
// }

namespace {
struct ParallelRegionReachable : public ModulePass {
  static char ID;

  explicit ParallelRegionReachable() : ModulePass(ID) {
    // initializeParallelRegionReachablePass(*PassRegistry::getPassRegistry());
  }

  bool runOnModule(llvm::Module &M) override {
    CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
    outs() << "callgraph analysis succceed!\n";
    // initialize GlobalFnStates to all Untouched
    initializeGlobalFnStates(CG);

    // initialize worklist
    SmallVector<CallGraphNode *, 8> workList;
    initializeWorkList(CG, workList);

    // while worklist non-empty,
    // populate
    for (size_t i = 0; i < workList.size(); ++i) {
        CallGraphNode *CGN = workList[i];
        assert(CGN && "worklist shouldn't have null callnode!");

        Function *Caller = CGN->getFunction();
        assert(Caller && "CallNode has null function!");
        if (Caller->isDeclaration()) {
            continue;
        }

        outs() << "pop CallNode " << Caller->getName() << "...\n";

        // get TapirTaskInfo for the caller function
        TaskInfo &TI = getAnalysis<TaskInfoWrapperPass>(*Caller).getTaskInfo();

        // for each callgraph node, traverse through each of its callsite
        for (CallGraphNode::CallRecord &CallRecord : *CGN) {
            // in the case of callback function, there is no callsite
            
            if (!CallRecord.first.hasValue()) {
                // TODO: this function has its address taken? 
                // call-edge type: reference edge
                ++NumCallback;
                if (CallRecord.second)
                    Callbacks.insert(CallRecord.second);
                continue;
            }
            // call-edge type: real call-edge
            assert(CallRecord.second && "encounter null second field in CallRecord!"); 
            // if (!CallRecord.second) {
            //     errs() << "encounter null second field in CallRecord!\n";
            //     continue;
            // }
            // assert(CallRecord.second && "encounter null second field in CallRecord!");
            Function *Callee = CallRecord.second->getFunction();
            if (!Callee) {
                // DBEUG: qsort.c has a callrecord whose second field is null, but callsite is non-null!
                outs() << "CallRecord contains null callee node! Callsite: ";
                if (const CallBase *CallSite = dyn_cast<CallBase>(*CallRecord.first)) {
                    CallSite->dump();
                }
                outs() << "\n";
                continue;
            }
            // assert(Callee && "CallRecord contains null callee node!");
            const CallBase *CallSite = dyn_cast<CallBase>(*CallRecord.first);
            assert(CallSite &&
                    "CallRecord doesn't have CallBase callsite instruction!");

            outs() << "  examing callsite at \n"; // << getLine(CallSite) << ":";
            CallSite->dump();
            outs() << "\n";
            
            // check if callsite is in a parallel-region
            const Task *T = TI[CallSite->getParent()];
            if (!T) {
                if (!Caller) {
                    errs() << "Callsite null"
                            << "->" << Callee->getName() << " has null task!\n";
                } else {
                    errs() << "Callsite " << Caller->getName() << "->"
                            << Callee->getName() << " has null task!\n";
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

    // set statistics
    printStatistic();
    return false;
    
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    // AU.addRequired<DominatorTreeWrapperPassF>();
    AU.addRequired<CallGraphWrapperPass>();
    AU.addRequired<TaskInfoWrapperPass>();
    AU.setPreservesAll();
  }
private: 
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
private: 
  FnState joinState(FnState s1, FnState s2) {
    switch(s1) {
    case ParallelRegionReachable::FnState::Both: {
      return s1;
    }
    case ParallelRegionReachable::FnState::Untouched: {
      return s2;
    }
    case ParallelRegionReachable::FnState::DefinitelyDAC: {
      switch(s2) {
        case ParallelRegionReachable::FnState::DefinitelyDAC: {
          return s2;
        }
        default: {
          return ParallelRegionReachable::FnState::Both;
        }
      }
    }
    case ParallelRegionReachable::FnState::DefinitelyEF: {
      switch(s2) {
        case ParallelRegionReachable::FnState::DefinitelyEF: {
          return s2;
        }
        default: {
          return ParallelRegionReachable::FnState::Both;
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

  void initializeGlobalFnStates(CallGraph& CG) {
    outs() << "calling initializeGlobalFnStates...\n";

    for (auto &it : CG) {
      const Function *F = it.first;
      if (!F)
        continue;
      GlobalFnStates[F] = ParallelRegionReachable::FnState::Untouched;
      // update global satistic: NumFn
      ++NumFn;

      (outs() << "Function " << F->getName()
                        << " state initialized!\n");
    }
    (outs() << "\n\n");
  }

  void initializeWorkList(CallGraph& CG, SmallVector<CallGraphNode *, 8>& workList) {
    outs() << "calling initializeWorkList...\n";
    for (auto &it : CG) {
      const Function *F = it.first;
      CallGraphNode *CGN = it.second.get();
      assert(CGN && "encounter null call graph node");
      if (!F)
        continue;
      workList.push_back(CGN);

      outs() << "Function " << F->getName()
                        << " pushed onto workList!\n";
    }
    outs() << "\n\n";
  }

  void printStatistic() {
    for (auto it : GlobalFnStates) {
        const Function *F = it.first;
        switch(it.second) {
        case ParallelRegionReachable::FnState::DefinitelyDAC: {
            ++NumDefinitelyDAC;
            outs() << "Function " << F->getName() << " is definitelyDAC at the end!\n";
            break;
        }
        case ParallelRegionReachable::FnState::DefinitelyEF: {
            ++NumDefinitelyEF;
            outs() << "Function " << F->getName() << " is definitelyEF at the end!\n";
            break;
        }
        case ParallelRegionReachable::FnState::Both: {
            ++NumBoth;
            outs() << "Function " << F->getName() << " is Both at the end!\n";
            break;
        }
        case ParallelRegionReachable::FnState::Untouched: {
            ++NumUntouched;
            outs() << "Function " << F->getName() << " is untouched at the end!\n";
            break;
        }
        }
    }
  }

  // @debug
  unsigned getLine(const CallBase *cs) {
    if (cs->getDebugLoc()) {
        return 0;
    }
    return cs->getDebugLoc().getLine();
  } 

private: 
  SmallSet<CallGraphNode *, 8> Callbacks;
  DenseMap<const Function *, FnState> GlobalFnStates;
};
} // namespace




char ParallelRegionReachable::ID = 0;
static RegisterPass<ParallelRegionReachable> X(PR_NAME,
                                      "Conduct CallGraph Analysis to determine "
                                      "outlining fashion of parallel-regions",
                                      false, true);

static const char pr_name[] = "Conduct CallGraph Analysis to determine "
                              "outlining fashion of functions called inside parallel-regions";
// static void* initializeParallelRegionPassOnce(PassRegistry &Registry) {
//     initializeTaskInfoWrapperPassPass(Registry);
//     initializeCallGraphWrapperPassPass(Registry);
//     PassInfo *PI = new PassInfo(                                             
//                     pr_name, PR_NAME, &ParallelRegionReachable::ID,
//                     PassInfo::NormalCtor_t(callDefaultCtor<ParallelRegion>), false, false);
//     Registry.registerPass(*PI, true); 
//     return PI;
// }
// static llvm::once_flag InitializeParallelRegionPassFlag; 
// void initializeParallelRegionPass(PassRegistry &Registry) {
//     llvm::call_once(InitializeParallelRegionPassFlag,
//                     initializeParallelRegionPassOnce, std::ref(Registry));
// }

///DEBUG: change ParallelRegion to a different name; there's likely a name conflict in llvm

// INITIALIZE_PASS(ParallelRegionReachable, PR_NAME, pr_name, false, false)
// INITIALIZE_PASS_BEGIN(ParallelRegionReachable, PR_NAME, pr_name, false, false) 
// INITIALIZE_PASS_DEPENDENCY(CallGraphWrapperPass)
// INITIALIZE_PASS_DEPENDENCY(TaskInfoWrapperPass)
// INITIALIZE_PASS_END(ParallelRegionReachable, PR_NAME, pr_name, false, false)

namespace llvm {
Pass *createParallelRegionPass() { return new ParallelRegionReachable(); }
}
