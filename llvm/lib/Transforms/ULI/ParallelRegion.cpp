#include "llvm/Transforms/Tapir/ParallelRegion.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/AbstractCallSite.h"
// #include "llvm/IR/CallSite.h" // deprecated
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
using namespace llvm;

#define PR_NAME "parallel-region"
#define DEBUG_TYPE "parallel-region-pass"

// cl::opt<bool> UseRuntimePFor(
//     "use-runtime-pfor", cl::init(false), cl::Hidden,
//     cl::desc("Insert a call into the Parallel Loop runtime to handle cilk_for loops"));

STATISTIC(NumDefinitelyDAC, "number of outlined functions that are definitely DAC outlining fashion.");
STATISTIC(NumUnsure, "number of outlined functions that are unsure of using either DAC or EF outlining fashion.");
STATISTIC(NumParallelRegions, "number of outlined functions that were originally parallel regions.");

class ParallelRegionImpl {
public: 
    ParallelRegionImpl(Module& M, CallGraph &CG) : M(M), CG(CG) {};
    bool run();
private: 
    bool runOnSCC(CallGraphSCC& SCC);
    bool isParallelRegion(CallGraphNode *CGN);
private:
    Module &M;
    CallGraph &CG;
}

bool ParallelRegionImpl::isParallelRegion(CallGraphNode *CGN) {
    Function *F = CGN->getFunction();
    assert(F && "encounter callgraph node with null function");

    // TODO: for each callnode in the callgrpah, 
    // identify fn attr using 
    // bool hasAttr = OutlineFcn->getFnAttribute("your-custom-attribute").getValueAsString()=="true";
    return false; 
}

bool ParallelRegionImpl::run() {
    SmallVector<Function *, 8> workList;
    SmallSet<Function *, 8> workSet;
    SmallVector<Function *, 8> definitelyDACOutlineFn;

    // init worklist;
    for (auto &CNP : CG) {
        CallGraphNode* CGNode = CNP.second.get();
        assert(CGNode && "encounter null call graph node");
        Function *F = CGNode->getFunction();
        if (isParallelRegion(CGNode)) {
            ++NumParallelRegions;
            workList.push_back(F);
            workSet.insert(F);
        }
    }
    // worklist algorithm through call graph, mark each callgraph node as DAC if it has a caller that's parallel region or DAC
    for (size_t i = 0; i < workList.size(); ++i) {
        Function *F = workList[i];
        if (workSet.find(F) != workSet.end())
            continue;
        workSet.insert(F);

        // iterate through call sites of F and add to worklist
        for (const User *User : F->users()) {
            auto *CB = dyn_cast<CallBase>(User);
            if (!CB || CB->getCalledFunction() != F)
                continue;
            Function *Caller = CB->getCaller();
            if (workSet.find(Caller) != workSet.end()) {
                workList.push_back(Caller);
            }
        }   
    }

    return false;
}

bool ParallelRegionImpl::runOnSCC(CallGraphSCC& SCC) {

    return false;
}


PreservedAnalyses ParallelRegionPass::run(Module& M, ModuleAnalysisManager& AM) {
    CallGraph &CG = AM.getResult<CallGraphAnalysis>(M);
    bool Changed = ParallelRegionImpl(M, CG).run();
    if (Changed) 
        return PreservedAnalyses::none();
    return PreservedAnalyses::all();
}

namespace {
struct ParallelRegion : ModulePass {
    static char ID;

    bool runOnModule(Module& M) override {
        CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();

        return ParallelRegionImpl(M, CG).run()
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired(CallGraphWrapperPass);
    AU.setPreservesAll();
    }
};
}


char ParallelRegion::ID = 0;

// static RegisterPass<> X("print-externalfnconstants",
//      "Print external fn callsites passed constants");
static const char pr_name[] = "Conduct CallGraph Analysis to determine outlining fashion of parallel-regions";
INITIALIZE_PASS_BEGIN(ParallelRegion, PR_NAME, pr_name,
                      false, true)
INITIALIZE_PASS_DEPENDENCY(CallGraphWrapperPass)
INITIALIZE_PASS_END(ParallelRegion, PR_NAME, pr_name,
                    false, true)