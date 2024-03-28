// ============ ParallelRegion.cpp ================

#include "llvm/Transforms/ULI/ParallelRegion.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"

#define PR_NAME "prr"
#define DEBUG_TYPE PR_NAME

using namespace llvm;

static cl::opt<std::string> PrrVerbose(
    "prrverbose", 
    cl::init("default"),
    cl::desc("prr analysis result printing: [func/loop/block]")
);

PRState joinState(PRState s1, PRState s2) {
    switch (s1) {
    case PRState::Both: {
        return s1;
    }
    case PRState::DefinitelyDAC: {
        switch (s2) {
        case PRState::DefinitelyDAC: {
        return s2;
        }
        default: {
        return PRState::Both;
        }
        }
    }
    case PRState::DefinitelyEF: {
        switch (s2) {
        case PRState::DefinitelyEF: {
        return s2;
        }
        default: {
        return PRState::Both;
        }
        }
    }
    default: {
        return s2;
    }
    };
}

StringRef llvm::printPRState(PRState prs) {
    switch (prs) {
        case PRState::Both: {
            return StringRef("both");
        }
        case PRState::DefinitelyDAC: {
            return StringRef("defdac");
        }
        case PRState::DefinitelyEF: {
            return StringRef("defef");
        }
        default: {
            return StringRef("untouched");
        }
    }
}

raw_ostream &llvm::operator<<(raw_ostream &os, PRState prs) {
    os << printPRState(prs);
}

//============ prr local dataflow analysis on each callnode ====================

void LocalDataflow::initializeBoundaryCondition(PRState initFS) {
    for (auto &BB : *F) {
    inLFS[&BB] = PRState::Untouched;
    outLFS[&BB] = PRState::Untouched;
    }
    const BasicBlock *Entry = &F->getEntryBlock();
    inLFS[Entry] = initFS;
}

void LocalDataflow::reduceInLFS(BasicBlock *BB, TaskInfo &TI) {
    const Task *T = TI[BB];
    if (T->getDetach() && TI.isTaskEntry(BB)) {
        // exception: for task entry block, set in[BB] = dac
        inLFS[BB] = PRState::DefinitelyDAC;
    } else {
        // not task entry block, reduce by joining out[pred]
        for (BasicBlock *Pred : predecessors(BB)) {
            inLFS[BB] = joinState(inLFS[BB], outLFS[Pred]);
        }
    }
}

void LocalDataflow::initializeLocalWorkList(SmallVector<BasicBlock *, 8> &workList,
                            SmallSet<BasicBlock *, 8> &workSet) {
    ReversePostOrderTraversal<Function *> RPO(F);
    for (auto I = RPO.begin(), E = RPO.end(); I != E; ++I) {
        workList.push_back(*I);
        workSet.insert(*I);
    }
}

void LocalDataflow::transferPRState(const BasicBlock *BB, TaskInfo &TI) {
    switch (inLFS[BB]) {
        case PRState::Both: {
            // if start of block can be reached by both parallel & serial region, bottom
            outLFS[BB] = PRState::Both;
            break;
        } 
        default: {
            // inLFS[BB] = Untouched / EF / DAC
            const Task *T = TI[BB];
            assert(T && "transferPRState found invalid TI!");
            
            if (T->getDetach()) {
                // BB is in parallel region
                unsigned TD = T->getTaskDepth();
                if (TD > 1) {
                    outLFS[BB] = PRState::DefinitelyDAC;
                } else {
                    assert (TD == 1 && "non-root task has 0 task depth!");
                    // if BB marks the exit of a depth-1 task, then stepping out
                    // would mean the termination of parallel region
                    if (T->isTaskExiting(BB)) {
                        // BB is the task exit into a serial region
                        outLFS[BB] = PRState::DefinitelyEF;
                    } else {
                        // BB not task exit, still inside a parallel region
                        outLFS[BB] = PRState::DefinitelyDAC;
                    }
                }
            } else {
                // BB is in serial region
                outLFS[BB] = PRState::DefinitelyEF;
            }
            break;
        }
    }
}

bool LocalDataflow::run(PRState initFS, TaskInfo &TI) {
    LLVM_DEBUG(dbgs() << "\nrun(" << F->getName() << ") with state " << printPRState(initFS) << "...\n");
    // refresh TaskInfo: DEBUG! You must get Caller's analysis result everytime, as the lifetime of a function pass is short

    // initialize all basic block PRState to Untouched & set entry block's
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
        LLVM_DEBUG(dbgs() << "    " << BB->getName() << ": in=" << printPRState(inLFS[BB]) << ", out=" << printPRState(outLFS[BB]));
        
        // update inLFS of BB from outLFS of predecessors of BB
        reduceInLFS(BB, TI);

        // transfer function: 
        // if BB is inside a parallel region, udpate with DefinitelyDAC
        // if BB is inside a serial region, update with DefinitelyEF
        PRState sOld = outLFS[BB];
        transferPRState(BB, TI);
        PRState sNew = outLFS[BB];
        LLVM_DEBUG(dbgs() << "-> in=" << printPRState(inLFS[BB]) << ", out=" << printPRState(outLFS[BB]) << "\n");

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

bool LocalDataflow::postProcess(CallGraphNode *CGN, FuncMapTy &FuncPRState,
                   SmallVector<CallGraphNode *, 8> &globalWorkList) {
    // LLVM_DEBUG(dbgs() << "  postProcess(" << Caller->getName() << ")...\n");
    bool Changed = false;
    // for each callee/callsite inside the callnode, update FuncPRState & globalWorkList
    for (CallGraphNode::CallRecord &CallRecord : *CGN) {
        if (!CallRecord.first.hasValue()) {
            // in the case of callback function, there is no callsite
            // call-edge type: reference edge
            LLVM_DEBUG(dbgs() << "!!!!!! FOUND RARE CALLBACK CASE !!!!!!!!!\n");
            continue;
        }

        // call-edge type: real call-edge
        assert(CallRecord.second && "encounter null second field in CallRecord!");
        
        Function *Callee = CallRecord.second->getFunction();
        if (!Callee) {
            continue;
        }
        const CallBase *CallSite = dyn_cast<CallBase>(*CallRecord.first);
        assert(CallSite &&
                "CallRecord doesn't have CallBase callsite instruction!");

        //   LLVM_DEBUG(dbgs() << "    examing callsite at " << CallSite->getParent()->getName() << ":");
        //   CallSite->dump();
        //   LLVM_DEBUG(dbgs() << "\n");

        // update state of callee node based on local pass results
        PRState sOld = FuncPRState[Callee];
        PRState sNew = joinState(sOld, inLFS[CallSite->getParent()]);
        FuncPRState[Callee] = sNew;

        // push Callee back on to worklist because of state change
        if (sOld != sNew) {
            // LLVM_DEBUG(dbgs() << "  <!> state change " << printPRState(sOld) << "-->" << printPRState(sNew) << "\n");
            globalWorkList.push_back(CallRecord.second);
            Changed = true;
        }
    }
    return Changed;
}

//=========== prr Analysis Pass core functionality ======================
void ParallelRegion::initializeLocalPRStates(CallGraph &CG) {
    LLVM_DEBUG(dbgs() << "initializeLocalPRStates...\n");
    for (auto &it : CG) {
        CallGraphNode *CGN = it.second.get();
        assert(CGN && "encounter null call graph node");
        Function *Caller = CGN->getFunction();
        // assert(Caller && "initializeLocalPRStates encounters callnode with null function!");
        if (!Caller || Caller->isDeclaration())
            continue;

        // initialize LocalDataflow for Caller function
        assert(Caller && "encounter null caller in initializeLocalPRStates!");
        LDF[Caller] = new LocalDataflow(Caller);
    }
}

void ParallelRegion::initializeFuncPRState(CallGraph &CG, 
                            std::function<LoopInfo &(Function &)> getLI, 
                            std::function<TaskInfo &(Function &)> getTI) {
    LLVM_DEBUG(dbgs() << "calling initializeFuncPRState...\n");
    // Collect Function pointer address argument =========================
    SmallSet<Function *, 8> FunInFunArgs;
    for (auto &it : CG) {
        Function *F = it.second->getFunction();
        if (!F) continue;

        for (auto I = inst_begin(F), E = inst_end(F); I != E; ++I) {
            if (const CallBase *CI = dyn_cast<CallBase>(&*I)) {
                for (unsigned i = 0; i < CI->arg_size(); ++i) {
                    Value *arg = CI->getArgOperand(i);
                    if (PointerType *ptrTy = dyn_cast<PointerType>(arg->getType())) {
                        if (ptrTy->getElementType()->isFunctionTy()) {
                            ConstantExpr *BitCast = dyn_cast<ConstantExpr>(arg);
                            assert(BitCast && BitCast->isCast() && "function pointer argument is not a bitcast!");
                            Function *Callee = dyn_cast<Function>(BitCast->getOperand(0));
                            FunInFunArgs.insert(Callee);
                        }
                    }
                }
            }
        }
    }
    // for (Function *Callee : FunInFunArgs) {
    //     if (Callee->isDeclaration()) {
    //         continue;
    //     }

    //     // for each top-level pfor in callee
    //     TaskInfo &TI = getTI(*Callee);
    //     LoopInfo &LI = getLI(*Callee);
    //     if (TI.isSerial()) 
    //         continue;
    //     for (Loop *TopLevelLoop : LI) {
    //         if (llvm::getTaskIfTapirLoopStructure(TopLevelLoop, &TI)) {
    //             // L is a top level TapirLoop with a state of BOTH 
    //             BasicBlock *H = TopLevelLoop->getHeader();
    //         }
    //     }
    // }

    // initialize function in-state to Untouch/Both
    for (auto &it : CG) {
        Function *F = it.second->getFunction();
        if (!F) 
            continue;
        if (FunInFunArgs.find(F) == FunInFunArgs.end()) {
            FuncPRState[F] = PRState::Untouched;
        } else {
            FuncPRState[F] = PRState::Both;
        }
    }
}

void ParallelRegion::initializeWorkList(CallGraph &CG, SmallVector<CallGraphNode *, 8> &workList) {
    LLVM_DEBUG(dbgs() << "initializeWorkList...\n");
    for (auto &it : CG) {
        const Function *F = it.first;
        CallGraphNode *CGN = it.second.get();
        assert(CGN && "encounter null call graph node");
        if (!F)
            continue;
        workList.push_back(CGN);

        //   LLVM_DEBUG(dbgs() << "Function " << F->getName() << " pushed onto workList!\n");
    }
}

void ParallelRegion::analyze(
        CallGraph &CG,
        std::function<LoopInfo &(Function &)> getLI,
        std::function<TaskInfo &(Function &)> getTI) {
    // initialize function to all Untouched
    initializeFuncPRState(CG, getLI, getTI);
    // initialize local dataflow pass,
    initializeLocalPRStates(CG);
    // initialize worklist
    SmallVector<CallGraphNode *, 8> workList;
    initializeWorkList(CG, workList);

    // main call-graph analysis logic: 
    //      for each callgraph node, run local dataflow anlaysis, 
    //      push back children nodes whose in-state changes, run until convergence
    for (size_t i = 0; i < workList.size(); ++i) {
        CallGraphNode *CGN = workList[i];
        assert(CGN && "worklist shouldn't have null callnode!");

        Function *Caller = CGN->getFunction();
        assert(Caller && "CallNode has null function!");
        if (Caller->isDeclaration()) {
            continue;
        }
        // rerun local dataflow analysis using new in-state
        LDF[Caller]->run(FuncPRState[Caller], getTI(*Caller));
        // for each callgraph node, traverse through each of its callsite
        LDF[Caller]->postProcess(CGN, FuncPRState, workList);
    }

    // populate block result & loop result
    for (auto &it : CG) {
        CallGraphNode *CGN = it.second.get();
        assert(CGN && "encounter null call graph node");
        Function *F = CGN->getFunction();
        if (!F || F->isDeclaration()) 
            continue;
        populateBlockPRState(F);
        populateLoopPRState(F, getTI(*F), getLI(*F));
    }
}

void ParallelRegion::populateBlockPRState(Function *F) {
    BlockPRState[F] = DenseMap<const BasicBlock *, PRState>();
    for (BasicBlock &BB : *F) {
        BlockPRState[F][&BB] = LDF[F]->getIn(&BB);
    }
}

void ParallelRegion::populateLoopPRState(Function *F, TaskInfo &TI, LoopInfo &LI) {
    LoopPRState[F] = DenseMap<const Loop *, PRState>();
    for (Loop *TopLevelLoop : LI) {
        for (Loop *L : post_order(TopLevelLoop)) {
            // assert(L->isLoopSimplifyForm() && "Loop is not simplied!");
            if (getTaskIfTapirLoopStructure(L, &TI)) {
                // tapir pfor
                /// DBEUG: bug find! I forgot to handle when parent loop is serial; 
                /// plus my dataflow propagation should already take care of this

                // if (L == TopLevelLoop) {
                //     LoopPRState[F][L] = LDF[F]->getIn(L->getHeader()); // DEBUG: original impl used getOut!
                // } else {
                //     LoopPRState[F][L] = PRState::DefinitelyDAC;
                // }
                LoopPRState[F][L] = LDF[F]->getIn(L->getHeader()); // DEBUG: original impl used getOut!
                
                // DEBUG 
                // if (F->getName() == "test_correctness") {
                //     assert(L->getHeader()->getName() == "pfor.cond.us.i" && "what?");
                //     if (L == TopLevelLoop) {
                //         outs() << "pfor.cond.us.i was a top level pfor!\n";
                //     } else {
                //         outs() << "pfor.cond.us.i is nested in " << TopLevelLoop->getHeader()->getName() << "!\n";
                //     }
                // }
                ////////
            }
        }
    }
}

PRState ParallelRegion::operator[](const Function* F) const { 
    return FuncPRState.lookup(F); 
}

PRState ParallelRegion::operator[](const Loop* L) const { 
    Function *F = L->getHeader()->getParent();
    const DenseMap<const Loop *, PRState> &LoopMap = LoopPRState.lookup(F);
    return LoopMap.lookup(L); 
}

PRState ParallelRegion::operator[](const BasicBlock* B) const {
    const Function *F = B->getParent();
    const DenseMap<const BasicBlock *, PRState> &BlockMap = BlockPRState.lookup(F);
    return BlockMap.lookup(B);
}

void ParallelRegion::printFuncPRState(raw_ostream &os) const {
    for (auto it : FuncPRState) { 
        const Function *F = it.first;
        assert(!F->isDeclaration() && "FuncPRState should not contain function declaration");
        PRState state = it.second;
        os << F->getName() << ": " << state << "\n";
    }
}

void ParallelRegion::printLoopPRState(raw_ostream &os) const {
    for (auto it : LoopPRState) { 
        const Function *F = it.first;
        assert(!F->isDeclaration() && "FuncPRState should not contain function declaration");
        os << ">> " << F->getName() << " :\n";
        
        DenseMap<const Loop*, PRState> &loopPRState = it.second;
        for (auto it : loopPRState) {
            const Loop *L = it.first;
            PRState state = it.second;
            os << "  " << L->getHeader()->getName() << ": " << state << "\n";
        }

        os << '\n';
    }
}

void ParallelRegion::printBlockPRState(raw_ostream &os) const {
    for (auto it : BlockPRState) {
        const Function *F = it.first;
        assert(!F->isDeclaration() && "FuncPRState should not contain function declaration");
        os << ">> " << F->getName() << " :\n";

        DenseMap<const BasicBlock *, PRState> &BlockMap = it.second;
        for (auto it : BlockMap) {
            const BasicBlock *BB = it.first;
            PRState state = it.second;
            os << "  " << BB->getName() << ": " << state << "\n";
        }

        os << "\n";
    }
}

void ParallelRegion::print(raw_ostream &os) const {
    os << "=================================\n";
    os << "Parallel Region Analysis result "; 
    os << "---------------------------------\n";
    if (PrrVerbose == "loop") {
        printLoopPRState(os);
    } else if (PrrVerbose == "block") {
        printBlockPRState(os);
    } else if (PrrVerbose == "func") {
        printFuncPRState(os);
    } else {
        assert(false && "PrrVerbose does not recognize this option");
    }
}

//=========== New Pass Manager Wrapper Pass ==================
ParallelRegion ParallelRegionAnalysis::run(Module &M, ModuleAnalysisManager &AM) {
    CallGraph &CG = AM.getResult<CallGraphAnalysis>(M);
    auto &FAM = AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
    auto getLI = [&](Function &F) -> LoopInfo& {
        return FAM.getResult<LoopAnalysis>(F);
    };
    auto getTI = [&](Function &F) -> TaskInfo& {
        return FAM.getResult<TaskAnalysis>(F);
    };

    ParallelRegion PR; 
    PR.analyze(CG, getLI, getTI); 

    // this anlaysis pass doesn't perform any transformation
    return PR;
}

//=========== Legacy Module Wrapper Pass definition =======================

bool ParallelRegionWrapperPass::runOnModule(llvm::Module &M) {    
    CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
    std::function<llvm::TaskInfo&(llvm::Function&)> getTI = 
        [&](llvm::Function &F) -> llvm::TaskInfo& {
        return getAnalysis<TaskInfoWrapperPass>(F).getTaskInfo();
    };
    std::function<llvm::LoopInfo&(llvm::Function&)> getLI = 
        [&](llvm::Function &F) -> llvm::LoopInfo& {
        return getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    };
    PR.analyze(CG, getLI, getTI);
    return false;
}

//=========== New Printer pass, register with opt =========================
PreservedAnalyses ParallelRegionPrinter::run(Module &M, ModuleAnalysisManager &AM) {
    AM.getResult<ParallelRegionAnalysis>(M).print(os);
    return PreservedAnalyses::all();
}

//=========== New Analysis Pass Manager registration ======================
llvm::AnalysisKey ParallelRegionAnalysis::Key;

llvm::PassPluginLibraryInfo getParallelRegionAnalysisPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, PR_NAME, LLVM_VERSION_STRING,
        [](PassBuilder &PB) {
            // register printer pass for opt -passes=print<parallel-region>
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &PM, auto ) {
                    if (Name == "print<parallel-region>") {
                        PM.addPass(ParallelRegionPrinter(llvm::errs()));
                        return true;
                    }
                    return false;
                }
            );
            // register analysis pass for getResult<ParalleRegionAnalysis>
            PB.registerAnalysisRegistrationCallback(
              [](ModuleAnalysisManager &AM) {
                AM.registerPass([&] { return llvm::ParallelRegionAnalysis(); });
              }
            );
        }
    };
};

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
    return getParallelRegionAnalysisPluginInfo();
}

//=========== Legacy Pass Manager in-tree registration ====================
char ParallelRegionWrapperPass::ID = 0;
static const char pr_name[] =
    "Conduct CallGraph Analysis to determine "
    "outlining fashion of functions called inside parallel-regions";
INITIALIZE_PASS_BEGIN(ParallelRegionWrapperPass, PR_NAME, pr_name, false, true) 
INITIALIZE_PASS_DEPENDENCY(CallGraphWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TaskInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_END(ParallelRegionWrapperPass, PR_NAME, pr_name, false, true)

namespace llvm {
ModulePass *createParallelRegionWrapperPass() { return new ParallelRegionWrapperPass(); }
} // namespace llvm
