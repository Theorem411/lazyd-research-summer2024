//===- ULIIntrinsicToExternCall.h - Emulate ULI intrinsics ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass replace ULI intrinsics with external calls to the ULI emulation
// library.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_EAGERD_TRANS_H
#define LLVM_TRANSFORMS_EAGERD_TRANS_H

#include "llvm/Pass.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

// Custom Pass
#include "llvm/Transforms/ULI/LazyReachingStoreReachableLoad.h"
#include "llvm/Transforms/ULI/LazyReachingDetachInst.h"
#include "llvm/Transforms/ULI/LazyLiveVariable.h"


#include <iostream>

#define OPTIMIZE_UNWIND
#define OPTIMIZE_UNWIND_FUNC

#define STEALENTRY_INDEX 1
#define GOTSTOLEN_INDEX 2

// Copy from unwind_scheduler.h
#define I_RBP 0   // Base pointer
#define I_RIP 1   // Instruction pointer
#define I_RSP 2   // Stack pointer
// Callee register
#define I_RBX 3
#define I_R12 4
#define I_R13 5
#define I_R14 6
#define I_R15 7
// Register
#define I_RDI 8
#define I_RSI 9
#define I_R8 10
#define I_R9 11
#define I_R10 12
#define I_R11 13
#define I_RDX 14
#define I_RCX 15
#define I_RAX 16

#define I_JOINCNT 17 // Join counter
#define I_NEWRSP 18 // New rsp of the parallel task
#define I_OWNER 19 // Who owns the job
#define I_READYCTX  20 // Location on the parallel task queue of the owner
#define I_ADDRLOC  21 // The address in the stack that store the location of work
#define I_DEQ_CMPLT 22
#define I_SLOWPATH_DEQUE 23
#define I_EXECUTEDBY_OWNER 24
#define I_ALREADY_RESUMED 25
#define WORKCTX_SIZE 64

using namespace std;

namespace llvm {

  struct EagerDTransPass : public PassInfoMixin<EagerDTransPass> {
  private:
    Value* lowerGrainsizeCall(CallInst *GrainsizeCall);
    void replaceUses(Instruction *liveVar, Instruction *slowLiveVar);
    void simplifyFcn(Function &F);
    void postProcessCfg(Function &F);    
    void createParallelRegion(Function& F, SmallVector<DetachInst*, 4> bbOrder, DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIPath, DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB, DenseMap<SyncInst *, SmallPtrSet<BasicBlock*, 8>>& RSIPath, SmallPtrSet<BasicBlock*, 32>& parallelRegions, SmallPtrSet<BasicBlock*, 32>& frontierParallelRegions, SmallPtrSet<BasicBlock*, 32>& exitParallelRegions);
    
    void initializeParallelCtx(Function& F, SmallVector<DetachInst*, 4> bbOrder, DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIPath, DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB, Value* readyctx, Value* ownerAlloc, SmallPtrSet<BasicBlock*, 32>& parallelRegions, SmallPtrSet<BasicBlock*, 32>& frontierParallelRegions);    
    void instrumentSlowPath(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,  SmallVector<SyncInst*, 8>& syncInsts, Value* ownerAlloc, Value* joincntrAlloc, Value* readyctx);
    
    void deinitializeParallelCtx(Function& F, Value* joincntrAlloc, Value* readyctx, SmallPtrSet<BasicBlock*, 32>& exitParallelRegions);
    void instrumentMainFcn(Function& F);

  public:    
    /// \return Preserved analyses of function \p F after transformation.
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

    void runAnalysisUsage(AnalysisUsage &AU) const;
    bool runImpl(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT,  DominanceFrontier &DF, LoopInfo &LI);
    bool runInitialization(Module &M);

  };
  /// \return An instance of created pass for legacy pass manager.
  Pass *createEagerDTransPass();

} // end namespace llvm


#endif // LLVM_TRANSFORMS_EAGERD_TRANS_H

