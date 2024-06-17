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

#ifndef LLVM_TRANSFORMS_LAZYD_TRANS_H
#define LLVM_TRANSFORMS_LAZYD_TRANS_H

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

// Can this cause performance improvemetn on classify kddcup?
// OPTIMIZE_FP: Used for removing FP
//#define OPTIMIZE_FP

// STICK_STACKXCGH_FUNC: Allow calling a function in the backtrack routine
#define STICK_STACKXCGH_FUNC

// OPTIMIZE_UNWIND: Only save the neccessary information during backtrack (doesn't seem to improve performance)
#define OPTIMIZE_UNWIND

// Enable the optimization above
#define OPTIMIZE_UNWIND_FUNC

// NO_UNWIND_POLLPFOR: Do not used a specialized polling for parallel-for (have not been tested)
#define NO_UNWIND_POLLPFOR

// UI_REGION is needed if you wan to use label to create a critical section in parallel-for
//#define UI_REGION

// PRL_LATER is used to parallelize parallel-ready loop only after all the DAC has been parallelized.
//#define PRL_LATER

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
#define I_LOC  20 // Location on the parallel task queue of the owner
#define I_ADDRLOC  21 // The address in the stack that store the location of work
#define I_DEQ_CMPLT 22
#define I_SLOWPATH_DEQUE 23
#define I_EXECUTEDBY_OWNER 24
#define WORKCTX_SIZE 64

using namespace std;

namespace llvm {

  struct LazyDTransPass : public PassInfoMixin<LazyDTransPass> {
  private:

    // Check if a function is spawning/forking function.
    bool bHaveFork;

    // Check if a function have dynamic alloca
    bool bHaveDynamicAlloca;

    // Check if function calls a function with more than 6 arguments
    bool bHaveCallFcn6Args;

    // Create the multiretcall from fast path to slow path
    void addPotentialJump(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder, ValueToValueMapTy& VMapSlowPath, Value* fromSlowPathAlloc, SSAUpdater& SSAUpdateWorkContext, DenseMap <DetachInst*, SmallPtrSet<AllocaInst*, 8>>& ReachingAllocSet, DominatorTree& DT);

    void insertCheckInContBlock(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder, ValueToValueMapTy& VMapSlowPath, Value* fromSlowPathAlloc,
                                DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB, SSAUpdater& SSAUpdateWorkContext);

    // Setup the datastructure (map, etc.)
    void intializeReconstructSsa(SmallVector<DetachInst*, 4>& bbOrder,
                                 DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                                 DenseMap <DetachInst*, SmallPtrSet<Instruction*, 8>>&  RequiredPhiNode,
                                 DenseMap<BasicBlock*, SmallPtrSet<Instruction*, 4>>& orig,
                                 DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& defsites,
                                 DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& PHIsites,
                                 SmallPtrSet<Instruction*, 4>& liveInstSet,
                                 ValueToValueMapTy& VMapSlowPath,
                                 ValueToValueMapTy& VMapSlowPathReverse,
                                 DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiUseMap);

    void insertPhiToReconsructSsa(IRBuilder<>& B,
                                  DominanceFrontier& DF,
                                  DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                                  DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& defsites,
                                  DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& PHIsites,
                                  SmallPtrSet<Instruction*, 4>& liveInstSet,
                                  ValueToValueMapTy& VMapSlowPathReverse,
                                  DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap);

    void renamePhiNodeToReconstructSsa(DominatorTree &DT,
                                       DominanceFrontier& DF,
                                       DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& PHIsites,
                                       SmallPtrSet<Instruction*, 4>& liveInstSet,
                                       DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap,
                                       DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiUseMap
                                       );
    void reconstructSsa(Function& F,
                        ValueToValueMapTy& VMapSlowPathReverse, ValueToValueMapTy& VMapSlowPath,
                        DominatorTree &DT, DominanceFrontier &DF,
                        DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap,
                        DenseMap <DetachInst*, SmallPtrSet<Instruction*, 8>>& RequiredPhiNode,
                        DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                        SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder);

    void insertPhiNodeInSlowPathCont(IRBuilder<> &B, Instruction* liveVar, Instruction* slowLiveVar, BasicBlock* slowContinueBB, BasicBlock * parent,
                                     DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap);

    void replaceUses(Instruction *liveVar, Instruction *slowLiveVar);

    void updateSSA(SSAUpdater& SSAUpdate, Instruction* inst2replace);

    // Merge slow path back to fast path
    void mergeSlowPathToFastPath(Function& F, SmallVector<SyncInst*, 8>& syncInsts, DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                                 ValueToValueMapTy& VMapSlowPath, DenseMap<BasicBlock*, BasicBlock*>& syncBB2syncPred);

    // For instruction in the fast path that always dominate the slow path (does not need a slow path),
    // replace the use of the slow path inst version with the one from the fast path
    void updateSlowVariables_2(Function& F,
                               ValueToValueMapTy& VMapSlowPathReverse, ValueToValueMapTy& VMapSlowPath,
                               DenseMap<BasicBlock*, BasicBlock*> syncBB2syncPred,
                               DominatorTree &DT, DominanceFrontier &DF,
                               DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap,
                               SmallPtrSet<Instruction*, 8>& RequiredPhiNode,
                               SmallPtrSet<Instruction*, 8>& PhiNodeInserted,
                               DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                               SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,
                               SmallVector<SyncInst*, 8>& syncInsts  );




    // For instruction in the fast path that always dominate the slow path (does not need a slow path),
    // replace the use of the slow path inst version with the one from the fast path
    void updateSlowVariables(Function& F,
                             ValueToValueMapTy& VMapSlowPathReverse, ValueToValueMapTy& VMapSlowPath,
                             DominatorTree &DT, DominanceFrontier &DF,
                             DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap,
                             DenseMap <DetachInst*, SmallPtrSet<Instruction*, 8>>& RequiredPhiNode,
                             DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                             SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder);
    // If a variable is located in the parallel path, then it needs a phi node
    void findRequiredPhiNodes(DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIPath,
                              DenseMap<SyncInst *, SmallPtrSet<BasicBlock*, 8>>& RSIPath,
                              DenseMap<BasicBlock*, BitVector> &MapBB2InVal,
                              DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                              SmallVector<SyncInst*, 8>& syncInsts,
                              SmallPtrSet<Instruction*, 8>& RequiredPhiNode);

    void simplifyFcn(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT);

    void replaceResultOfMultiRetCallWithRetpad(Function &F);

    // Clone BasicBlock
    // If load and store is from the slow path, set it to volatile
    void cloneBasicBlock(Function &F, SmallVector<BasicBlock*, 8>& bb2clones, ValueToValueMapTy& VMapSlowPath, ValueToValueMapTy& VMapSlowPathReverse,
                         SmallPtrSet<AllocaInst*, 8>& AllocaSet );


    void postProcessCfg(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT, SmallPtrSet<AllocaInst*, 8>& AllocaSet);

    /// Copied from CilkABI.cpp
    /// \brief Lower a call to get the grainsize of this Tapir loop.
    ///
    /// The grainsize is computed by the following equation:
    ///
    ///     Grainsize = min(2048, ceil(Limit / (8 * workers)))
    ///
    /// This computation is inserted into the preheader of the loop.
    Value* lowerGrainsizeCall(CallInst *GrainsizeCall);

    void convertTapirIrToBr(Function &F);


    BasicBlock* createUnwindHandler(Function &F, Value* locAlloc, Value* ownerAlloc, Value* bHaveUnwindAlloc, SmallVector<DetachInst*, 4>& bbOrder, ValueToValueMapTy& VMapSlowPath, ValueToValueMapTy& VMapGotStolenPath);

    // Get the live variables after the detached block (live out)
    // Create a store for it.
    // Create a load for it in the restore path
    // Add potential jump to got stolen handler
    void createGotStolenHandler(SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,
                                Value* locAlloc, Value* ownerAlloc,
                                DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>& LVout,
                                DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                                ValueToValueMapTy& VMapSlowPath,
                                ValueToValueMapTy& VMapGotStolenPath
                                );

    BasicBlock * createGotStolenHandlerBB(DetachInst& Detach, BasicBlock* contBB, Value* locAlloc, Value* ownerAlloc);

    void instrumentPushPop(Function& F, SmallVector<BasicBlock*, 8>& bb2clones);

    void instrumentSlowPath(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,
                            Value* locAlloc, Value* ownerAlloc, Value* bHaveUnwindAlloc, Value* fromSlowPathAlloc, SmallVector<SyncInst*, 8>& syncInsts, ValueToValueMapTy&  VMapSlowPath,
                            DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB,
                            SSAUpdater& SSAUpdateWorkContext);

    void instrumentMainFcn(Function& F);
    StructType* RequestChannelTy = nullptr;
    StructType* ResponseChannelTy = nullptr;

    enum RequestChannelFields
    {
      sendThreadId = 0,
      padding_char,
      potentialParallelTask,
      inLoop,
      padding
    };

  public:
    /// \return Preserved analyses of function \p F after transformation.
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

    void runAnalysisUsage(AnalysisUsage &AU) const;
    bool runImpl(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT,  DominanceFrontier &DF, LoopInfo &LI);
    bool runInitialization(Module &M);


  };

  /// \return An instance of created pass for legacy pass manager.
  Pass *createLazyDTransPass();


} // end namespace llvm


#endif // LLVM_TRANSFORMS_LAZYD_TRANS_H

