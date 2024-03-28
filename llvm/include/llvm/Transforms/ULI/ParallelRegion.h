//===- ParallelRegion.h -  ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass performs callgraph analysis to determine outlining strategy for 
// parallel regions as outlined functions.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_PARALLEL_REGION_H
#define LLVM_TRANSFORMS_PARALLEL_REGION_H

#include "llvm/Pass.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Transforms/Utils/TapirUtils.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/TapirTaskInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/InitializePasses.h"
#include "llvm/PassInfo.h"
#include "llvm/PassRegistry.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"

namespace llvm {

//========= Parallel region state representation ========================
enum class PRState {
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

StringRef printPRState(PRState prs);
raw_ostream &operator<<(raw_ostream &os, PRState prs);

using FuncMapTy = DenseMap<const Function *, PRState>;
using LoopMapTy = DenseMap<const Function *, DenseMap<const Loop *, PRState>>; 
using BlockMapTy = DenseMap<const Function *, DenseMap<const BasicBlock *, PRState>>;

//============ PRR analysis Result definition ============================
struct LocalDataflow {
    LocalDataflow(Function *F) : F(F) {}
    /**
    * LocalDataflow::run: 
    *   Perform forward dataflow analysis of global PRState inside a certain callnode
    *   called each time callnode's PRState changed
    */
    bool run(PRState initFS, TaskInfo &TI);

    bool postProcess(CallGraphNode *CGN, FuncMapTy &FuncPRState,
                    SmallVector<CallGraphNode *, 8> &globalWorkList);

    PRState getIn(const BasicBlock *B) {
        return inLFS[B];
    }

    PRState getOut(const BasicBlock *B) {
        return outLFS[B];
    }
private:
    // initialization functionalities for local dataflow anlaysis
    void initializeBoundaryCondition(PRState initFS);
    void initializeLocalWorkList(SmallVector<BasicBlock *, 8> &workList,
                                SmallSet<BasicBlock *, 8> &workSet);
    // dataflow reduction function 
    void reduceInLFS(BasicBlock *BB, TaskInfo &TI);
    // dataflow transfer function
    void transferPRState(const BasicBlock *BB, TaskInfo &TI);
private:
    Function *F;
    // result state should be only be read after the dataflow analysis is run
    using BlockMapTy = DenseMap<const BasicBlock *, PRState>;
    BlockMapTy inLFS;
    BlockMapTy outLFS;
};

struct ParallelRegion {
    ParallelRegion() {}
    ~ParallelRegion() {}

    // core functionality of prr analysis
    void analyze(CallGraph &CG,
                 std::function<LoopInfo &(Function &)>, 
                 std::function<TaskInfo &(Function &)>);

    // user query interface
    PRState operator[](const Function* F) const;
    PRState operator[](const Loop* L) const;
    PRState operator[](const BasicBlock* B) const;

    // print function
    void printFuncPRState(raw_ostream &os) const;
    void printLoopPRState(raw_ostream &os) const;
    void printBlockPRState(raw_ostream &os) const;
    void print(raw_ostream &os) const;
private: 
    // initialization functionalities for callgraph level worklist algorithm
    void initializeLocalPRStates(CallGraph &CG);
    void initializeFuncPRState(CallGraph &CG, 
                                std::function<LoopInfo &(Function &)> getLI, 
                                std::function<TaskInfo &(Function &)> getTI);
    void initializeWorkList(CallGraph &CG, SmallVector<CallGraphNode *, 8> &workList);

    // populate BlockPRState & LoopPRState after callgraph level worklist algorithm converges
    void populateBlockPRState(Function *F);
    void populateLoopPRState(Function *F, TaskInfo &TI, LoopInfo &LI);
private:
    FuncMapTy FuncPRState;
    LoopMapTy LoopPRState;
    BlockMapTy BlockPRState; // the in-state of each basic block

    DenseMap<const Function*, LocalDataflow *> LDF;
};

//=========== Legacy Module Wrapper Pass definition =======================
struct ParallelRegionWrapperPass : public ModulePass {
    static char ID;

    explicit ParallelRegionWrapperPass() : ModulePass(ID) {
        llvm::initializeParallelRegionWrapperPassPass(*PassRegistry::getPassRegistry());
    }

    bool runOnModule(Module &M) override;

    void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.addRequired<CallGraphWrapperPass>();
        AU.addRequired<LoopInfoWrapperPass>();
        AU.addRequired<TaskInfoWrapperPass>();
        AU.setPreservesAll();
    }

    ParallelRegion &getParallelRegion() { return PR; }
    const ParallelRegion &getParallelRegion() const { return PR; }

private: 
    ParallelRegion PR;
};

//=========== New Pass Manager declare Analysis & Printer Pass ============

struct ParallelRegionAnalysis : public AnalysisInfoMixin<ParallelRegionAnalysis> {
    using Result = ParallelRegion;
    ParallelRegion run(Module &M, ModuleAnalysisManager &);
private:
    friend AnalysisInfoMixin<ParallelRegionAnalysis>;
    static AnalysisKey Key; 
};

struct ParallelRegionPrinter : public PassInfoMixin<ParallelRegionPrinter> {
    explicit ParallelRegionPrinter(raw_ostream &os) : os(os) {};
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &);
private: 
    raw_ostream &os;
};

/// \return An instance of created pass for legacy pass manager.
ModulePass *createParallelRegionWrapperPass();

}

#endif // LLVM_TRANFORMS_PARALLEL_REGION_PASS_H