// ============ ParallelRegion.cpp ================

#include "llvm/Transforms/ULI/ParallelRegion.h"
#include "llvm/Transforms/Utils/TapirUtils.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringRef.h"
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
#include "llvm/Support/JSON.h"
#include "llvm/Support/CommandLine.h"


#define PR_NAME "prr"
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
STATISTIC(NumPForTopLevelDefinitelyDAC,
          "NumPForTopLevelDefinitelyDAC  "
          "number of top-level pfor that doesn't need counter-assisted outlining"
          " because it's definitely DAC");
STATISTIC(NumPForDefinitelyEF, 
          "NumPForDefinitelyEF  "
          "number of parallel-for that doesn't need counter-assisted outlining"
          " because it's definitely EF");
STATISTIC(NumPForTopLevelDefinitelyEF,
          "NumPForTopLevelDefinitelyEF  "
          "number of top-level pfor that doesn't need counter-assisted outlining"
          " because it's definitely EF");
STATISTIC(NumPForBoth, 
          "NumPForBoth          "
          "number of parallel-for that will need a global counter to choose "
          "outlining strategy because it can be reached by both parallel and "
          "and serial region control-flow path");
STATISTIC(NumPForTopLevelBoth,
          "NumPForTopLevelBoth  "
          "number of top-level pfor that will need a global counter to choose "
          "outlining strategy because it can be reached by both parallel and "
          "and serial region control-flow path");
STATISTIC(NumPForUntouched, 
          "NumPForUntouched    "
          "number of pfor that are still untouched by the dataflow analysis"
          ". DEBUG: this number should be 0!!!");

cl::opt<std::string> TestName(
    "test", 
    cl::init("default"), 
    cl::Hidden,
    cl::desc("name of benchmark test case"));


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
// @debug
unsigned getLine(const CallBase *cs) {
    if (cs->getDebugLoc()) {
        return 0;
    }
    return cs->getDebugLoc().getLine();
}

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
  case FnState::Both: {
    return s1;
  }
  case FnState::DefinitelyDAC: {
    switch (s2) {
    case FnState::DefinitelyDAC: {
      return s2;
    }
    default: {
      return FnState::Both;
    }
    }
  }
  case FnState::DefinitelyEF: {
    switch (s2) {
    case FnState::DefinitelyEF: {
      return s2;
    }
    default: {
      return FnState::Both;
    }
    }
  }
  default: {
    return s2;
  }
  };
}

StringRef ppFnState(FnState s) {
    switch (s) {
        case FnState::Both: {
            return StringRef("both");
        }
        case FnState::DefinitelyDAC: {
            return StringRef("defdac");
        }
        case FnState::DefinitelyEF: {
            return StringRef("defef");
        }
        default: {
            return StringRef("untouched");
        }
    }
}

using GlobalFnStatesTy = DenseMap<Function *, FnState>;
using LocalFnStatesTy = DenseMap<const BasicBlock *, FnState>;
struct LocalFnStatePass {
  LocalFnStatePass(Function *Caller)
      : Caller(Caller) {}
  /**
   * LocalFnStatePass::run: 
   *   Perform forward dataflow analysis of global FnState inside a certain callnode
   *   called each time callnode's FnState changed
  */
  bool run(FnState initFS, TaskInfo &TI) {
    outs() << "\nrun(" << Caller->getName() << ") with state " << ppFnState(initFS) << "...\n";
    // refresh TaskInfo: DEBUG! You must get Caller's analysis result everytime, as the lifetime of a function pass is short

    // initialize all basic block FnState to Untouched & set entry block's
    // boundary condition
    initializeBoundaryCondition(initFS);
    // put all basic blocks in caller in reverse post-order into workList
    SmallVector<BasicBlock *, 8> workList;
    SmallSet<BasicBlock *, 8> workSet;
    initializeLocalWorkList(workList, workSet);

    for (size_t i = 0; i < workList.size(); ++i) {
      // pop workList & update workSet
      BasicBlock *BB = workList[i];
      bool erased = workSet.erase(BB);
      assert(erased && "Found basicblock in workList but not in workSet!");

      outs() << "    " << BB->getName() << ": in=" << ppFnState(inLFS[BB]) << ", out=" << ppFnState(outLFS[BB]);

      // update inLFS of BB from outLFS of predecessors of BB
      reduceInLFS(BB);

      // transfer function: 
      // if BB is inside a parallel region, udpate with DefinitelyDAC
      // if BB is inside a serial region, update with DefinitelyEF
      FnState sOld = outLFS[BB];
      const Task *T = TI[BB];

      assert(T && "Callsite contains null task. There should be a root task!");
      if (T->getDetach()) {
        outs() << " =p=> ";
        // callsite is in a parallel region
        transferFnState(BB, FnState::DefinitelyDAC);
      } else {
        outs() << " =s=> ";
        // callsite is in a serial region because no Task OR Task is serial
        transferFnState(BB, FnState::DefinitelyEF);
      }
      FnState sNew = outLFS[BB];

      outs() << "in=" << ppFnState(inLFS[BB]) << ", out=" << ppFnState(outLFS[BB]) << "\n";

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
                   SmallVector<CallGraphNode *, 8> &globalWorkList, 
                   SmallSet<CallGraphNode *, 8> &Callbacks) {
    outs() << "  postProcess(" << Caller->getName() << ")...\n";
    bool Changed = false;
    // for each callee/callsite inside the callnode, update GlobalFnStates & globalWorkList
    for (CallGraphNode::CallRecord &CallRecord : *CGN) {
      if (!CallRecord.first.hasValue()) {
        // in the case of callback function, there is no callsite
        // call-edge type: reference edge
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
        // outs() << "CallRecord contains null callee node! Callsite: ";
        // if (const CallBase *CallSite = dyn_cast<CallBase>(*CallRecord.first)) {
        //   CallSite->dump();
        // }
        continue;
      }
      const CallBase *CallSite = dyn_cast<CallBase>(*CallRecord.first);
      assert(CallSite &&
             "CallRecord doesn't have CallBase callsite instruction!");

      outs() << "    examing callsite at " << CallSite->getParent()->getName() << ":";
      CallSite->dump();
      outs() << "\n";

      // update state of callee node based on local pass results
      FnState sOld = GlobalFnStates[Callee];
      FnState sNew = joinState(sOld, outLFS[CallSite->getParent()]);
      GlobalFnStates[Callee] = sNew;

      // push Callee back on to worklist because of state change
      if (sOld != sNew) {
        outs() << "  <!> state change " << ppFnState(sOld) << "-->" << ppFnState(sNew) << "\n";
        globalWorkList.push_back(CallRecord.second);
        Changed = true;
      }
    }
    return Changed;
  }
  
  FnState getLocalFnState(BasicBlock *BB) {
    // called after run()
    return outLFS[BB];
  }

private:
  void initializeBoundaryCondition(FnState initFS) {
    outs() << "  initializeBoundaryCondition...\n";
    for (auto &BB : *Caller) {
      inLFS[&BB] = FnState::Untouched;
      outLFS[&BB] = FnState::Untouched;
    }
    const BasicBlock *Entry = &Caller->getEntryBlock();
    inLFS[Entry] = initFS;
  }

  void initializeLocalWorkList(SmallVector<BasicBlock *, 8> &workList,
                               SmallSet<BasicBlock *, 8> &workSet) {
    outs() << "  initializeLocalWorkList(" << Caller->getName() << ")...\n";
    ReversePostOrderTraversal<Function *> RPO(Caller);
    for (auto I = RPO.begin(), E = RPO.end(); I != E; ++I) {
      workList.push_back(*I);
      workSet.insert(*I);
    }
  }
  void reduceInLFS(BasicBlock *BB) {
    for (BasicBlock *Pred : predecessors(BB)) {
        inLFS[BB] = joinState(inLFS[BB], outLFS[Pred]);
    }
  }

  void transferFnState(const BasicBlock *BB, FnState newState) {
    outLFS[BB] = joinState(inLFS[BB], newState);
  }

private:
  Function *Caller;
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
    // outs() << "callgraph analysis succceed!\n";
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

      //   outs() << "pop CallNode " << Caller->getName() << "...\n";

      // rerun LocalFnStatePass to perform CFG dataflow analysis using new entry
      // condition
      if (Fn2LFP.find(Caller) == Fn2LFP.end())
        continue;
      TaskInfo &TI = getAnalysis<TaskInfoWrapperPass>(*Caller).getTaskInfo();
      Fn2LFP[Caller]->run(GlobalFnStates[Caller], TI);

      // for each callgraph node, traverse through each of its callsite
      bool Changed = Fn2LFP[Caller]->postProcess(CGN, GlobalFnStates, workList, Callbacks);
    }

    // set statistics
    printStatistic();
    
    // output json
    outputStatistic();
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
      Function *F = it.second->getFunction();
      if (!F)
        continue;
      GlobalFnStates[F] = FnState::Untouched;
      // update global satistic: NumFn
      ++NumFn;

    //   (outs() << "Function " << F->getName() << " state initialized!\n");
    }
  }

  void initializeLocalFnStates(CallGraph &CG) {
    outs() << "initializeLocalFnStates...\n";
    for (auto &it : CG) {
      CallGraphNode *CGN = it.second.get();
      assert(CGN && "encounter null call graph node");
      Function *Caller = CGN->getFunction();
      if (!Caller)
        continue;
      if (Caller->isDeclaration()) {
        continue;
      }
    //   outs() << "Function " << Caller->getName()
    //          << " registered by localFnStatePass!\n";

      // get analysis results of Function Passes
      assert(Caller && "encounter null caller in initializeLocalFnStates!");
      
      Fn2LFP[Caller] = new LocalFnStatePass(Caller);
    }
  }

  void initializeWorkList(CallGraph &CG,
                          SmallVector<CallGraphNode *, 8> &workList) {
    outs() << "initializeWorkList...\n";
    for (auto &it : CG) {
      const Function *F = it.first;
      CallGraphNode *CGN = it.second.get();
      assert(CGN && "encounter null call graph node");
      if (!F)
        continue;
      workList.push_back(CGN);

    //   outs() << "Function " << F->getName() << " pushed onto workList!\n";
    }
  }

  void printStatistic();
  
  void outputStatistic();

private:
  SmallSet<CallGraphNode *, 8> Callbacks;
  GlobalFnStatesTy GlobalFnStates;
  DenseMap<const Function *, LocalFnStatePass *> Fn2LFP;
};

void ParallelRegionReachable::printStatistic() {
    // print && udpate statistics for functions 
    outs() << "\n>>> printing global fn states...\n";
    for (auto it : GlobalFnStates) {
        Function *F = it.first;
        outs() << F->getName() << ": " << ppFnState(it.second) << "\n";
    }

    for (auto it : GlobalFnStates) {
      const Function *F = it.first;
      switch (it.second) {
      case FnState::DefinitelyDAC: {
        ++NumDefinitelyDAC;
        // outs() << "Function " << F->getName()
        //        << " is definitelyDAC at the end!\n";
        break;
      }
      case FnState::DefinitelyEF: {
        ++NumDefinitelyEF;
        // outs() << "Function " << F->getName()
        //        << " is definitelyEF at the end!\n";
        break;
      }
      case FnState::Both: {
        ++NumBoth;
        // outs() << "Function " << F->getName() << " is Both at the end!\n";
        break;
      }
      case FnState::Untouched: {
        ++NumUntouched;
        // outs() << "Function " << F->getName() << " is untouched at the end!\n";
        break;
      }
      }
    }

    // print states inside all functions
    outs() << "\n>>> printing local fn states for each function...\n";
    for (auto it : GlobalFnStates) {
        Function *F = it.first;
        outs() << F->getName() << ": --------------------------------\n";
        
        for (auto &BB : *F) {
            errs() << BB.getName() << ": " << ppFnState(Fn2LFP[F]->getLocalFnState(&BB)) << "\n";
        }
        outs() << "\n";
    }

    // update statistics for TapirLoops / pfors
    for (auto it : GlobalFnStates) {
      Function *F = it.first;
      if (Fn2LFP.find(F) == Fn2LFP.end())
        continue;
      outs() << "\n" << F->getName() << ":\n";
      TaskInfo &TI = getAnalysis<TaskInfoWrapperPass>(*F).getTaskInfo();
      LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*F).getLoopInfo();
      
      for (Task *T : TI) {
        if (T->getDetach()) {
            T->dump();
            outs() << "\n";
        }
      }
      // if F only have rootTask, no pfor, skip
      if (TI.isSerial()) 
        continue;
    
      for (Loop *TopLevelLoop : LI) {
        for (Loop *L : post_order(TopLevelLoop)) {
          Task *T = getTaskIfTapirLoop(L, &TI);
          if (!T) {
            // L not a TapirLoop
            continue;
          }

          // L is a TapirLoop
          ++NumPFor;
          L->dump();
          outs() << "\n";
          if (L == TopLevelLoop) {
            ++NumPForTopLevel;
            // top-level TapirLoop needs precaution about their FnState
            FnState LoopLFS = Fn2LFP[F]->getLocalFnState(L->getHeader());
            switch (LoopLFS) {
                case FnState::DefinitelyDAC: {
                    ++NumPForDefinitelyDAC;
                    ++NumPForTopLevelDefinitelyDAC;
                    break;
                } 
                case FnState::DefinitelyEF: {
                    ++NumPForDefinitelyEF;
                    ++NumPForTopLevelDefinitelyEF;
                    break;
                } 
                case FnState::Both: {
                    ++NumPForBoth;
                    ++NumPForTopLevelBoth;
                    break;
                } 
                case FnState::Untouched: {
                    ++NumPForUntouched;
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

    // update statistic for NumCallBacks
    for (auto CB : Callbacks) {
        outs() << CB->getFunction()->getName() << " is a callback function!\n";
        ++NumCallback;
    }
  }



void ParallelRegionReachable::outputStatistic() {
    json::Object jsonObj;
    jsonObj["NumFn"] = static_cast<uint64_t>(NumFn);
    jsonObj["NumDefinitelyDAC"] = static_cast<uint64_t>(NumDefinitelyDAC);
    jsonObj["NumDefinitelyEF"] = static_cast<uint64_t>(NumDefinitelyEF);
    jsonObj["NumBoth"] = static_cast<uint64_t>(NumBoth);
    jsonObj["NumUntouched"] = static_cast<uint64_t>(NumUntouched);
    jsonObj["NumCallback"] = static_cast<uint64_t>(NumCallback);

    jsonObj["NumPFor"] = static_cast<uint64_t>(NumPFor);
    jsonObj["NumPForDefinitelyDAC"] = static_cast<uint64_t>(NumPForDefinitelyDAC);
    jsonObj["NumPForDefinitelyEF"] = static_cast<uint64_t>(NumPForDefinitelyEF);
    jsonObj["NumPForBoth"] = static_cast<uint64_t>(NumPForBoth);
    jsonObj["NumPForUntouched"] = static_cast<uint64_t>(NumPForUntouched);

    jsonObj["NumPForTopLevel"] = static_cast<uint64_t>(NumPForTopLevel);
    jsonObj["NumPForTopLevelDefinitelyDAC"] = static_cast<uint64_t>(NumPForTopLevelDefinitelyDAC);
    jsonObj["NumPForTopLevelDefinitelyEF"] = static_cast<uint64_t>(NumPForTopLevelDefinitelyEF);
    jsonObj["NumPForTopLevelBoth"] = static_cast<uint64_t>(NumPForTopLevelBoth);

    //
    json::Value jsonVal = std::move(jsonObj);

    // output to file
    std::string FileName = TestName + ".json";
    outs() << "\n------\nFileName: " << FileName << "\n";
    std::error_code EC;
    raw_fd_ostream file(FileName, EC);
    if (EC) {
        errs() << "Error opening file: " << EC.message() << "\n";
        return;
    }
    file << formatv("{0:2}", jsonVal);
}


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
