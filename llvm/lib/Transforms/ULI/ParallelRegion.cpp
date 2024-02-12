#include "llvm/Transforms/ULI/ParallelRegion.h"
#include "llvm/Transforms/Utils/TapirUtils.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/TapirTaskInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
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
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#define PR_NAME "parallel-region-reachable"
#define DEBUG_TYPE PR_NAME

using namespace llvm;

STATISTIC(NumFn, 
          "NumFn                "
          "number of functions in module");
STATISTIC(NumDefinitelyDAC,
          "NumDefinitelyDAC     "
          "number of functions that are definitely called within a parallel "
          "region, and thus must adopt DAC as its outline strategy.");
STATISTIC(NumDefinitelyEF,
          "NumDefinitelyEF      "
          "number of functions that are definitely called within a serial "
          "region, and thus can adopt EF as its outline strategy.");
STATISTIC(NumBoth, 
          "NumBoth              "
          "number of functions that are witnessed to be called in "
          "both parallel and serial region, and thus must use a "
          "global counter to decide its outline stategy.");
STATISTIC(NumUntouched,
          "NumUntouched         "
          "number of functions untouched by the end of this call-graph analysis,"
          " usually root function in the callgraph.");
STATISTIC(NumCallback, 
          "NumCallback          "
          "number of callback functions");
STATISTIC(NumPFor, 
          "NumPFor              "
          "number of parallel-for loops");
STATISTIC(NumPForTopLevel, 
          "NumPForTopLevel      "
          "number of top-level pfor loops");
STATISTIC(NumPForDefinitelyDAC, 
          "NumPForDefinitelyDAC "
          "number of parallel-for that doesn't need counter-assisted outlining"
          " because it's definitely DAC");
STATISTIC(NumPforTopLevelDefinitelyDAC,
          "NumPforTopLevelDefinitelyDAC\n"
          "                     "
          "number of top-level pfor that doesn't need counter-assisted outlining"
          " because it's definitely DAC");
STATISTIC(NumPForDefinitelyEF, 
          "NumPForDefinitelyEF  "
          "number of parallel-for that doesn't need counter-assisted outlining"
          " because it's definitely EF");
STATISTIC(NumPforTopLevelDefinitelyEF,
          "NumPforTopLevelDefinitelyEF\n"
          "                     "
          "number of top-level pfor that doesn't need counter-assisted outlining"
          " because it's definitely EF");
STATISTIC(NumPForBoth, 
          "NumPForBoth          "
          "number of parallel-for that will need a global counter to choose "
          "outlining strategy because it can be reached by both parallel and "
          "and serial region control-flow path");
STATISTIC(NumPforTopLevelBoth,
          "NumPforTopLevelBoth\n"
          "                     "
          "number of top-level pfor that will need a global counter to choose "
          "outlining strategy because it can be reached by both parallel and "
          "and serial region control-flow path");
STATISTIC(NumPforUntouched, 
          "NumPforUntouched    "
          "number of pfor that are still untouched by the dataflow analysis"
          ". DEBUG: this number should be 0!!!");
// DEBUG: Note on how to check the function attribute defined in LoopSpawningTI
//   Function *F = CGN->getFunction();
//   //   assert(F && "encounter callgraph node with null function");
//   // TODO: for each callnode in the callgrpah, identify fn attr using
//   return F && F->getFnAttribute("parallel-region").getValueAsString() ==
//   "true";

// PreservedAnalyses ParallelRegionPass::run(Module &M,
//                                           ModuleAnalysisManager &AM) {
// // auto &FAM =
// AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
// //   DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(M);
//   CallGraph &CG = AM.getResult<CallGraphAnalysis>(M);
//   bool Changed = ParallelRegionImpl(M, CG, TI).run();
//   if (Changed)
//     return PreservedAnalyses::none();
//   return PreservedAnalyses::all();
// }

namespace {

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
FnState joinState(FnState s1, FnState s2) {
  switch (s1) {
  case ParallelRegionReachable::FnState::Both: {
    return s1;
  }
  case ParallelRegionReachable::FnState::Untouched: {
    return s2;
  }
  case ParallelRegionReachable::FnState::DefinitelyDAC: {
    switch (s2) {
    case ParallelRegionReachable::FnState::DefinitelyDAC: {
      return s2;
    }
    default: {
      return ParallelRegionReachable::FnState::Both;
    }
    }
  }
  case ParallelRegionReachable::FnState::DefinitelyEF: {
    switch (s2) {
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

using GlobalFnStatesTy = DenseMap<const Function *, FnState>;
using LocalFnStatesTy = DenseMap<const BasicBlock *, FnState>;
struct LocalFnStatePass {
  LocalFnStatePass(const Function *Caller, TaskInfo &TI)
      : Caller(Caller), TI(TI) {}
  /**
   * LocalFnStatePass::run: 
   *   Perform forward dataflow analysis of global FnState inside a certain callnode
   *   called each time callnode's FnState changed
  */
  bool run(FnState initFS) {
    // initialize all basic block FnState to Untouched & set entry block's
    // boundary condition
    initializeLocalFnState(initFS);
    // put all basic blocks in caller in reverse post-order into workList
    SmallVector<BasicBlock *, 8> workList;
    SmallSet<BasicBlock *, 8> workSet;
    initializeLocalWorkList(workList, workSet);

    for (size_t i = 0; i < workList.size(); ++i) {
      // pop workList & update workSet
      BasicBlock *BB = workList[i];
      bool erased = workSet.erase(BB);
      assert(erased && "Found basicblock in workList but not in workSet!");

      // update inLFS of BB from outLFS of predecessors of BB
      reduceInLFS(BB);

      // transfer function: 
      // if BB is inside a parallel region, udpate with DefinitelyDAC
      // if BB is inside a serial region, update with DefinitelyEF
      FnState sOld = outLFS[BB];
      const Task *T = TI[BB];
      assert(T && "Callsite contains null task. There should be a root task!");
      if (T->isSerial()) {
        // callsite is in a serial region
        transferFnState(BB, FnState::DefinitelyEF);
      } else {
        // callsite is in a parallel region
        transferFnState(BB, FnState::DefinitelyDAC);
      }
      FnState sNew = outLFS[BB];

      // if local state changed, push successors back to the worklist
      if (sOld != sNew) {
        // Out state changed! Push successors back onto the workList
        for (BasicBlock *Succ : successors(BB)) {
            // ensure no-duplicate workList at any time
            if (workSet.find(Succ) == workSet.end()) {
                workList.push_back(Succ);
                workSet.insert(Succ);
            }
        }
      }
    }

    return false;
  }

  bool postProcess(CallGraphNode *CGN, GlobalFnStatesTy &GlobalFnStates,
                   SmallVector<CallGraphNode *, 8> &globalWorkList) {
    // for each callee/callsite inside the callnode, update GlobalFnStates & globalWorkList
    for (CallGraphNode::CallRecord &CallRecord : *CGN) {
      if (!CallRecord.first.hasValue()) {
        // in the case of callback function, there is no callsite
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
      Function *Callee = CallRecord.second->getFunction();
      if (!Callee) {
        // DBEUG: qsort.c has a callrecord whose second field is null, but
        // callsite is non-null!
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

      // update state of callee node based on local pass results
      FnState sOld = GlobalFnStates[Callee];
      FnState sNew = joinState(sOld, outLFS[CallSite->getParent()]);

      // push Callee back on to worklist because of state change
      if (sOld != sNew) {
        globalWorkList.push_back(CallRecord.second);
      }
    }
  }
  
  FnState getLocalFnState(BasicBlock *BB) {
    // called after run()
    return outLFS[BB];
  }

private:
  void initializeLocalFnState(FnState initFS) {
    outs() << "initialize boundary conditions of inLFS & outLFS\n";
    for (auto &BB : Caller) {
      inLFS[&BB] = FnState::Untouched;
      outLFS[&BB] = FnState::Untouched;
    }
    const BasicBlock *Entry = &Caller->getEntryBlock();
    inLFS[Entry] = initFS;
    outs() << "\n\n";
  }

  void initializeLocalWorkList(SmallVector<BasicBlock *, 8> &workList,
                               SmallSet<BasicBlock *, 8> &workSet) {
    outs() << "calling initializeWorkList inside " << F->getName() << "...\n";
    ReversePostOrderTraversal<Function *> RPO(Caller);
    for (auto I = RPO.begin(), E = RPO.end(); I != E; ++I) {
      workList.push_back(*I);
      workSet.insert(*I);
    }
    outs() << "\n\n";
  }
  void reduceInLFS(const BasicBlock *BB) {
    for (BasicBlock *Pred : predecessors(BB)) {
        inLFS[BB] = joinState(inLFS[BB], outLFS[Pred]);
    }
  }

  void transferFnState(const BasicBlock *BB, FnState newState) {
    outLFS[BB] = joinState(inLFS[BB], newState);
  }

private:
  Function *Caller;
  TaskInfo &TI;
  // result state should be readable after the dataflow analysis is run
  LocalFnStatesTy inLFS;
  LocalFnStatesTy outLFS;
};

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

    // initialize LocalFnState,
    initializeLocalFnStates(CG);
    // initialize worklist
    SmallVector<CallGraphNode *, 8> workList;
    initializeWorkList(CG, workList);

    // while callnode worklist non-empty
    for (size_t i = 0; i < workList.size(); ++i) {
      CallGraphNode *CGN = workList[i];
      assert(CGN && "worklist shouldn't have null callnode!");

      Function *Caller = CGN->getFunction();
      assert(Caller && "CallNode has null function!");
      if (Caller->isDeclaration()) {
        continue;
      }

      outs() << "pop CallNode " << Caller->getName() << "...\n";

      // rerun LocalFnStatePass to perform CFG dataflow analysis using new entry
      // condition
      Fn2LFP[Caller]->run(GlobalFnState[Caller]);

      // for each callgraph node, traverse through each of its callsite
      bool Changed = Fn2LFP[Caller]->postProcess(CGN, GlobalFnStates, workList);
    }

    // set statistics
    printStatistic();
    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    // AU.addRequired<DominatorTreeWrapperPassF>();
    AU.addRequired<CallGraphWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<TaskInfoWrapperPass>();
    AU.setPreservesAll();
  }

private:
  void initializeGlobalFnStates(CallGraph &CG) {
    outs() << "calling initializeGlobalFnStates...\n";

    for (auto &it : CG) {
      const Function *F = it.first;
      if (!F)
        continue;
      GlobalFnStates[F] = ParallelRegionReachable::FnState::Untouched;
      // update global satistic: NumFn
      ++NumFn;

      (outs() << "Function " << F->getName() << " state initialized!\n");
    }
    (outs() << "\n\n");
  }

  void initializeLocalFnStates(CallGraph &CG) {
    for (auto &it : CG) {
      const Function *Caller = it.first;
      CallGraphNode *CGN = it.second.get();
      assert(CGN && "encounter null call graph node");
      if (!Caller)
        continue;
      if (Caller->isDeclaration()) {
        continue;
      }
      outs() << "Function " << Caller->getName()
             << " registered by localFnStatePass!\n";
      // run Local
      TaskInfo &TI = getAnalysis<TaskInfoWrapperPass>(*Caller).getTaskInfo();
      TaskInfoMap[Caller] = &TI;
      LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*Caller).getLoopInfo();
      LoopInfoMap[Caller] = &LI;
      Fn2LFP[Caller] = new LocalFnStatePass(Caller, TI);
    }
  }

  void initializeWorkList(CallGraph &CG,
                          SmallVector<CallGraphNode *, 8> &workList) {
    outs() << "calling initializeWorkList...\n";
    for (auto &it : CG) {
      const Function *F = it.first;
      CallGraphNode *CGN = it.second.get();
      assert(CGN && "encounter null call graph node");
      if (!F)
        continue;
      workList.push_back(CGN);

      outs() << "Function " << F->getName() << " pushed onto workList!\n";
    }
    outs() << "\n\n";
  }

  void printStatistic() {
    // udpate statistics for functions 
    for (auto it : GlobalFnStates) {
      const Function *F = it.first;
      switch (it.second) {
      case ParallelRegionReachable::FnState::DefinitelyDAC: {
        ++NumDefinitelyDAC;
        outs() << "Function " << F->getName()
               << " is definitelyDAC at the end!\n";
        break;
      }
      case ParallelRegionReachable::FnState::DefinitelyEF: {
        ++NumDefinitelyEF;
        outs() << "Function " << F->getName()
               << " is definitelyEF at the end!\n";
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

    // update statistics for TapirLoops / pfors
    for (auto it : GlobalFnStates) {
      const Function *F = it.first;
      TaskInfo *TI = TaskInfoMap[F]; 
      assert(TI && "Found null TI form TaskInfoMap!");
      if (TI->isSerial()) 
        // not parallel-region, not pfor
        continue;

      LoopInfo *LI = LoopInfoMap[F];
      for (Loop *TopLevelLoop : *LI) {
        for (Loop *L : post_order(TopLevelLoop)) {
          Task *T = getTaskIfTapirLoop(L, TI);
          if (!T) {
            // L not a TapirLoop
            continue;
          }
          // L is a TapirLoop
          ++NumPFor;
          if (L == TopLevelLoop) {
            ++NumPForTopLevel;
            // top-level TapirLoop needs precaution about their FnState
            FnState LoopLFS = Fn2LP[F]->getLocalFnState(L->getHeader());
            switch (LoopLFS) {
                case FnState::DefinitelyDAC: {
                    ++NumPForDefinitelyDAC;
                    ++NumPforTopLevelDefinitelyDAC;
                    break;
                } 
                case FnState::DefinitelyEF: {
                    ++NumPForDefinitelyEF;
                    ++NumPforTopLevelDefinitelyEF;
                    break;
                } 
                case FnState::Both: {
                    ++NumPForBoth;
                    ++NumPforTopLevelBoth;
                    break;
                } 
                case FnState::Untouched: {
                    ++NumPforUntouched;
                    break;
                } 
            }
          } else {
            // inner TapirLoops are by default definitelyDAC
            ++NumPForDefinitelyDAC;
          }

        }
      }
    }
  }

//   FnState getState(Function *F) {
//     assert(GlobalFnStates.find(F) != GlobalFnStates.end() &&
//            "GlobalFnStates doesn't contain function when getState is called!");
//     return GlobalFnStates[F];
//   }

//   void updateState(Function *F, FnState stateNew) {
//     assert(GlobalFnStates.find(F) != GlobalFnStates.end() &&
//            "F is not registered in GlobalFnStates!");
//     FnState stateOld = GlobalFnStates[F];
//     GlobalFnStates[F] = joinState(stateOld, stateNew);
//   }
  // @debug
  unsigned getLine(const CallBase *cs) {
    if (cs->getDebugLoc()) {
      return 0;
    }
    return cs->getDebugLoc().getLine();
  }

private:
  SmallSet<CallGraphNode *, 8> Callbacks;
  GlobalFnStatesTy GlobalFnStates;
  DenseMap<const Function *, LocalFnStatePass *> Fn2LFP;
  DenseMap<const Function *, TaskInfo *> TaskInfoMap;
  DenseMap<const Function *, LoopInfo *> LoopInfoMap;
};
} // namespace

char ParallelRegionReachable::ID = 0;
static RegisterPass<ParallelRegionReachable>
    X(PR_NAME,
      "Conduct CallGraph Analysis to determine "
      "outlining fashion of parallel-regions",
      false, true);

static const char pr_name[] =
    "Conduct CallGraph Analysis to determine "
    "outlining fashion of functions called inside parallel-regions";
// static void* initializeParallelRegionPassOnce(PassRegistry &Registry) {
//     initializeTaskInfoWrapperPassPass(Registry);
//     initializeCallGraphWrapperPassPass(Registry);
//     PassInfo *PI = new PassInfo(
//                     pr_name, PR_NAME, &ParallelRegionReachable::ID,
//                     PassInfo::NormalCtor_t(callDefaultCtor<ParallelRegion>),
//                     false, false);
//     Registry.registerPass(*PI, true);
//     return PI;
// }
// static llvm::once_flag InitializeParallelRegionPassFlag;
// void initializeParallelRegionPass(PassRegistry &Registry) {
//     llvm::call_once(InitializeParallelRegionPassFlag,
//                     initializeParallelRegionPassOnce, std::ref(Registry));
// }

/// DEBUG: change ParallelRegion to a different name; there's likely a name
/// conflict in llvm

// INITIALIZE_PASS(ParallelRegionReachable, PR_NAME, pr_name, false, false)
// INITIALIZE_PASS_BEGIN(ParallelRegionReachable, PR_NAME, pr_name, false,
// false) INITIALIZE_PASS_DEPENDENCY(CallGraphWrapperPass)
// INITIALIZE_PASS_DEPENDENCY(TaskInfoWrapperPass)
// INITIALIZE_PASS_END(ParallelRegionReachable, PR_NAME, pr_name, false, false)

namespace llvm {
Pass *createParallelRegionPass() { return new ParallelRegionReachable(); }
} // namespace llvm
