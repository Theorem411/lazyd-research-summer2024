//===- LoopInfo.cpp - Natural Loop Calculator -----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the LoopInfo class that is used to identify natural loops
// and determine the loop depth of various nodes of the CFG.  Note that the
// loops identified may actually be several natural loops that share the same
// header node... not just a single natural loop.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/IVDescriptors.h"
#include "llvm/Analysis/LoopInfoImpl.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopNestAnalysis.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/MemorySSAUpdater.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/PrintPasses.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
using namespace llvm;

// Explicitly instantiate methods in LoopInfoImpl.h for IR-level Loops.
template class llvm::LoopBase<BasicBlock, Loop>;
template class llvm::LoopInfoBase<BasicBlock, Loop>;

// Always verify loopinfo if expensive checking is enabled.
#ifdef EXPENSIVE_CHECKS
bool llvm::VerifyLoopInfo = true;
#else
bool llvm::VerifyLoopInfo = false;
#endif
static cl::opt<bool, true>
    VerifyLoopInfoX("verify-loop-info", cl::location(VerifyLoopInfo),
                    cl::Hidden, cl::desc("Verify loop info (time consuming)"));

//===----------------------------------------------------------------------===//
// Loop implementation
//

// Returns true if the basic block Succ that succeeds BB is the unwind
// destination of a detach.
static bool succIsDetachUnwind(const BasicBlock *BB, const BasicBlock *Succ) {
  if (const DetachInst *DI = dyn_cast<DetachInst>(BB->getTerminator()))
    return Succ == DI->getUnwindDest();
  return false;
}

/// Returns true if the given instruction performs a taskframe resume, false
/// otherwise.
static bool isDetachedRethrow(const Instruction *I,
                              const Value *SyncReg = nullptr) {
  if (const InvokeInst *II = dyn_cast<InvokeInst>(I))
    if (const Function *Called = II->getCalledFunction())
      if (Intrinsic::detached_rethrow == Called->getIntrinsicID())
        if (!SyncReg || (SyncReg == II->getArgOperand(0)))
          return true;
  return false;
}

/// Returns true if the given instruction performs a taskframe resume, false
/// otherwise.
static bool isTaskFrameResume(const Instruction *I,
                              const Value *TaskFrame = nullptr) {
  if (const InvokeInst *II = dyn_cast<InvokeInst>(I))
    if (const Function *Called = II->getCalledFunction())
      if (Intrinsic::taskframe_resume == Called->getIntrinsicID())
        if (!TaskFrame || (TaskFrame == II->getArgOperand(0)))
          return true;
  return false;
}

/// Returns true if the given basic block is a placeholder successor of a
/// taskframe.resume or detached.rethrow.
static bool isTapirPlaceholderSuccessor(const BasicBlock *B) {
  for (const BasicBlock *Pred : predecessors(B)) {
    if (!isDetachedRethrow(Pred->getTerminator()) &&
        !isTaskFrameResume(Pred->getTerminator()))
      return false;

    const InvokeInst *II = dyn_cast<InvokeInst>(Pred->getTerminator());
    if (B != II->getNormalDest())
      return false;
  }
  return true;
}

/// Helper method to find loop-exit blocks that are contained within tasks
/// spawned within the loop.
static void getTaskExitsHelper(BasicBlock *TaskEntry, const Loop *L,
                               SmallPtrSetImpl<BasicBlock *> &TaskExits) {
  // Traverse the CFG to find the exit blocks from SubT.
  SmallVector<BasicBlock *, 4> Worklist;
  SmallPtrSet<BasicBlock *, 4> Visited;
  Worklist.push_back(TaskEntry);
  while (!Worklist.empty()) {
    BasicBlock *BB = Worklist.pop_back_val();
    if (!Visited.insert(BB).second)
      continue;

    // Record any block found in the task that is not contained in the loop
    if (!L->contains(BB))
      TaskExits.insert(BB);

    // Stop the CFG traversal at any reattach or detached.rethrow
    if (isa<ReattachInst>(BB->getTerminator()) ||
        isDetachedRethrow(BB->getTerminator()))
      continue;

    // If we encounter a detach, only add its continuation and unwind
    // destination
    if (DetachInst *DI = dyn_cast<DetachInst>(BB->getTerminator())) {
      Worklist.push_back(DI->getContinue());
      if (DI->hasUnwindDest())
        Worklist.push_back(DI->getUnwindDest());
      continue;
    }

    // For all other basic blocks, traverse all successors
    for (BasicBlock *Succ : successors(BB))
      Worklist.push_back(Succ);
  }
}

/// getTaskExits - Get basic blocks that are outside of the loop, based on CFG
/// analysis, but inside tasks created within the loop.
///
void Loop::getTaskExits(SmallPtrSetImpl<BasicBlock *> &TaskExits) const {
  SmallVector<BasicBlock *, 4> TaskEntriesToCheck;
  for (auto *BB : blocks())
    if (DetachInst *DI = dyn_cast<DetachInst>(BB->getTerminator()))
      if (DI->hasUnwindDest())
        if (!contains(DI->getUnwindDest()))
          TaskEntriesToCheck.push_back(DI->getDetached());

  for (BasicBlock *TaskEntry : TaskEntriesToCheck)
    getTaskExitsHelper(TaskEntry, this, TaskExits);
}

/// getExitingBlocks - Return all blocks inside the loop that have successors
/// outside of the loop.  These are the blocks _inside of the current loop_
/// which branch out.  The returned list is always unique.
///
void Loop::getExitingBlocks(SmallVectorImpl<BasicBlock *> &ExitingBlocks,
                            bool IgnoreDetachUnwind) const {
  assert(!isInvalid() && "Loop not in a valid state!");
  for (const auto BB : blocks())
    for (const auto *Succ : children<BasicBlock *>(BB))
      if (!contains(Succ)) {
        if (IgnoreDetachUnwind && succIsDetachUnwind(BB, Succ))
          continue;
        // Not in current loop? It must be an exit block.
        ExitingBlocks.push_back(BB);
        break;
      }
}

/// getExitingBlock - If getExitingBlocks would return exactly one block,
/// return that block. Otherwise return null.
BasicBlock *Loop::getExitingBlock(bool IgnoreDetachUnwind) const {
  assert(!isInvalid() && "Loop not in a valid state!");
  SmallVector<BasicBlock *, 8> ExitingBlocks;
  getExitingBlocks(ExitingBlocks, IgnoreDetachUnwind);
  if (ExitingBlocks.size() == 1)
    return ExitingBlocks[0];
  return nullptr;
}

/// getExitBlocks - Return all of the successor blocks of this loop.  These
/// are the blocks _outside of the current loop_ which are branched to.
///
void Loop::getExitBlocks(
    SmallVectorImpl<BasicBlock *> &ExitBlocks) const {
  assert(!isInvalid() && "Loop not in a valid state!");
  std::vector<BasicBlock *> Blocks(block_begin(), block_end());
  SmallPtrSet<BasicBlock *, 4> TaskExits;
  getTaskExits(TaskExits);
  Blocks.insert(Blocks.end(), TaskExits.begin(), TaskExits.end());

  for (const auto BB : Blocks)
    for (auto *Succ : children<BasicBlock *>(BB))
      if (!contains(Succ) && !TaskExits.count(Succ) &&
          !isTapirPlaceholderSuccessor(Succ))
        // Not in current loop? It must be an exit block.
        ExitBlocks.push_back(Succ);
}

/// getExitBlock - If getExitBlocks would return exactly one block,
/// return that block. Otherwise return null.
BasicBlock *Loop::getExitBlock() const {
  assert(!isInvalid() && "Loop not in a valid state!");
  SmallVector<BasicBlock *, 8> ExitBlocks;
  getExitBlocks(ExitBlocks);
  if (ExitBlocks.size() == 1)
    return ExitBlocks[0];
  return nullptr;
}

bool Loop::hasDedicatedExits() const {
  // Each predecessor of each exit block of a normal loop is contained
  // within the loop.
  SmallVector<BasicBlock *, 4> UniqueExitBlocks;
  getUniqueExitBlocks(UniqueExitBlocks);
  SmallPtrSet<BasicBlock *, 4> TaskExits;
  getTaskExits(TaskExits);

  for (BasicBlock *EB : UniqueExitBlocks)
    for (BasicBlock *Predecessor : children<Inverse<BasicBlock *>>(EB))
      if (!contains(Predecessor) && !TaskExits.count(Predecessor))
        return false;
  // All the requirements are met.
  return true;
}

// Helper function to get unique loop exits. Pred is a predicate pointing to
// BasicBlocks in a loop which should be considered to find loop exits.
template <typename PredicateT>
void getUniqueExitBlocksOutsideTasksHelper(
    const Loop *L, SmallVectorImpl<BasicBlock *> &ExitBlocks, PredicateT Pred) {
  assert(!L->isInvalid() && "Loop not in a valid state!");
  SmallPtrSet<BasicBlock *, 32> Visited;
  std::vector<BasicBlock *> Blocks(L->block_begin(), L->block_end());
  SmallPtrSet<BasicBlock *, 4> TaskExits;
  L->getTaskExits(TaskExits);
  Blocks.insert(Blocks.end(), TaskExits.begin(), TaskExits.end());

  auto Filtered = make_filter_range(Blocks, Pred);
  for (BasicBlock *BB : Filtered) {
    for (BasicBlock *Successor : children<BasicBlock *>(BB))
      if (!L->contains(Successor) && !TaskExits.count(Successor) &&
          !isTapirPlaceholderSuccessor(Successor))
        if (Visited.insert(Successor).second)
          ExitBlocks.push_back(Successor);
  }
}

void Loop::getUniqueExitBlocks(
    SmallVectorImpl<BasicBlock *> &ExitBlocks) const {
  getUniqueExitBlocksOutsideTasksHelper(
      this, ExitBlocks, [](const BasicBlock *BB) { return true; });
}

void Loop::getUniqueNonLatchExitBlocks(
    SmallVectorImpl<BasicBlock *> &ExitBlocks) const {
  const BasicBlock *Latch = getLoopLatch();
  assert(Latch && "Latch block must exists");
  getUniqueExitBlocksOutsideTasksHelper(
      this, ExitBlocks, [Latch](const BasicBlock *BB) { return BB != Latch; });
}

BasicBlock *Loop::getUniqueExitBlock() const {
  SmallVector<BasicBlock *, 8> UniqueExitBlocks;
  getUniqueExitBlocks(UniqueExitBlocks);
  if (UniqueExitBlocks.size() == 1)
    return UniqueExitBlocks[0];
  return nullptr;
}

/// getExitEdges - Return all pairs of (_inside_block_,_outside_block_).
void Loop::getExitEdges(SmallVectorImpl<Edge> &ExitEdges) const {
  assert(!isInvalid() && "Loop not in a valid state!");
  std::vector<BasicBlock *> Blocks(block_begin(), block_end());
  SmallPtrSet<BasicBlock *, 4> TaskExits;
  getTaskExits(TaskExits);
  Blocks.insert(Blocks.end(), TaskExits.begin(), TaskExits.end());

  for (const auto BB : Blocks)
    for (auto *Succ : children<BasicBlock *>(BB))
      if (!contains(Succ) && !TaskExits.count(Succ) &&
          !isTapirPlaceholderSuccessor(Succ))
        // Not in current loop? It must be an exit block.
        ExitEdges.emplace_back(BB, Succ);
}

bool Loop::isLoopInvariant(const Value *V) const {
  if (const Instruction *I = dyn_cast<Instruction>(V))
    return !contains(I);
  return true; // All non-instructions are loop invariant
}

bool Loop::hasLoopInvariantOperands(const Instruction *I) const {
  return all_of(I->operands(), [this](Value *V) { return isLoopInvariant(V); });
}

bool Loop::makeLoopInvariant(Value *V, bool &Changed, Instruction *InsertPt,
                             MemorySSAUpdater *MSSAU) const {
  if (Instruction *I = dyn_cast<Instruction>(V))
    return makeLoopInvariant(I, Changed, InsertPt, MSSAU);
  return true; // All non-instructions are loop-invariant.
}

bool Loop::makeLoopInvariant(Instruction *I, bool &Changed,
                             Instruction *InsertPt,
                             MemorySSAUpdater *MSSAU) const {
  // Test if the value is already loop-invariant.
  if (isLoopInvariant(I))
    return true;
  if (!isSafeToSpeculativelyExecute(I))
    return false;
  if (I->mayReadFromMemory())
    return false;
  // EH block instructions are immobile.
  if (I->isEHPad())
    return false;
  // Determine the insertion point, unless one was given.
  if (!InsertPt) {
    BasicBlock *Preheader = getLoopPreheader();
    // Without a preheader, hoisting is not feasible.
    if (!Preheader)
      return false;
    InsertPt = Preheader->getTerminator();
  }
  // Don't hoist instructions with loop-variant operands.
  for (Value *Operand : I->operands())
    if (!makeLoopInvariant(Operand, Changed, InsertPt, MSSAU))
      return false;

  // Hoist.
  I->moveBefore(InsertPt);
  if (MSSAU)
    if (auto *MUD = MSSAU->getMemorySSA()->getMemoryAccess(I))
      MSSAU->moveToPlace(MUD, InsertPt->getParent(),
                         MemorySSA::BeforeTerminator);

  // There is possibility of hoisting this instruction above some arbitrary
  // condition. Any metadata defined on it can be control dependent on this
  // condition. Conservatively strip it here so that we don't give any wrong
  // information to the optimizer.
  I->dropUnknownNonDebugMetadata();

  Changed = true;
  return true;
}

bool Loop::getIncomingAndBackEdge(BasicBlock *&Incoming,
                                  BasicBlock *&Backedge) const {
  BasicBlock *H = getHeader();

  Incoming = nullptr;
  Backedge = nullptr;
  pred_iterator PI = pred_begin(H);
  assert(PI != pred_end(H) && "Loop must have at least one backedge!");
  Backedge = *PI++;
  if (PI == pred_end(H))
    return false; // dead loop
  Incoming = *PI++;
  if (PI != pred_end(H))
    return false; // multiple backedges?

  if (contains(Incoming)) {
    if (contains(Backedge))
      return false;
    std::swap(Incoming, Backedge);
  } else if (!contains(Backedge))
    return false;

  assert(Incoming && Backedge && "expected non-null incoming and backedges");
  return true;
}

PHINode *Loop::getCanonicalInductionVariable() const {
  BasicBlock *H = getHeader();

  BasicBlock *Incoming = nullptr, *Backedge = nullptr;
  if (!getIncomingAndBackEdge(Incoming, Backedge))
    return nullptr;

  // Loop over all of the PHI nodes, looking for a canonical indvar.
  for (BasicBlock::iterator I = H->begin(); isa<PHINode>(I); ++I) {
    PHINode *PN = cast<PHINode>(I);
    if (ConstantInt *CI =
            dyn_cast<ConstantInt>(PN->getIncomingValueForBlock(Incoming)))
      if (CI->isZero())
        if (Instruction *Inc =
                dyn_cast<Instruction>(PN->getIncomingValueForBlock(Backedge)))
          if (Inc->getOpcode() == Instruction::Add && Inc->getOperand(0) == PN)
            if (ConstantInt *CI = dyn_cast<ConstantInt>(Inc->getOperand(1)))
              if (CI->isOne())
                return PN;
  }
  return nullptr;
}

/// Get the latch condition instruction.
ICmpInst *Loop::getLatchCmpInst() const {
  if (BasicBlock *Latch = getLoopLatch())
    if (BranchInst *BI = dyn_cast_or_null<BranchInst>(Latch->getTerminator()))
      if (BI->isConditional())
        return dyn_cast<ICmpInst>(BI->getCondition());

  return nullptr;
}

/// Return the final value of the loop induction variable if found.
static Value *findFinalIVValue(const Loop &L, const PHINode &IndVar,
                               const Instruction &StepInst) {
  ICmpInst *LatchCmpInst = L.getLatchCmpInst();
  if (!LatchCmpInst)
    return nullptr;

  Value *Op0 = LatchCmpInst->getOperand(0);
  Value *Op1 = LatchCmpInst->getOperand(1);
  if (Op0 == &IndVar || Op0 == &StepInst)
    return Op1;

  if (Op1 == &IndVar || Op1 == &StepInst)
    return Op0;

  return nullptr;
}

Optional<Loop::LoopBounds> Loop::LoopBounds::getBounds(const Loop &L,
                                                       PHINode &IndVar,
                                                       ScalarEvolution &SE) {
  InductionDescriptor IndDesc;
  if (!InductionDescriptor::isInductionPHI(&IndVar, &L, &SE, IndDesc))
    return None;

  Value *InitialIVValue = IndDesc.getStartValue();
  Instruction *StepInst = IndDesc.getInductionBinOp();
  if (!InitialIVValue || !StepInst)
    return None;

  const SCEV *Step = IndDesc.getStep();
  Value *StepInstOp1 = StepInst->getOperand(1);
  Value *StepInstOp0 = StepInst->getOperand(0);
  Value *StepValue = nullptr;
  if (SE.getSCEV(StepInstOp1) == Step)
    StepValue = StepInstOp1;
  else if (SE.getSCEV(StepInstOp0) == Step)
    StepValue = StepInstOp0;

  Value *FinalIVValue = findFinalIVValue(L, IndVar, *StepInst);
  if (!FinalIVValue)
    return None;

  return LoopBounds(L, *InitialIVValue, *StepInst, StepValue, *FinalIVValue,
                    SE);
}

using Direction = Loop::LoopBounds::Direction;

ICmpInst::Predicate Loop::LoopBounds::getCanonicalPredicate() const {
  BasicBlock *Latch = L.getLoopLatch();
  assert(Latch && "Expecting valid latch");

  BranchInst *BI = dyn_cast_or_null<BranchInst>(Latch->getTerminator());
  assert(BI && BI->isConditional() && "Expecting conditional latch branch");

  ICmpInst *LatchCmpInst = dyn_cast<ICmpInst>(BI->getCondition());
  assert(LatchCmpInst &&
         "Expecting the latch compare instruction to be a CmpInst");

  // Need to inverse the predicate when first successor is not the loop
  // header
  ICmpInst::Predicate Pred = (BI->getSuccessor(0) == L.getHeader())
                                 ? LatchCmpInst->getPredicate()
                                 : LatchCmpInst->getInversePredicate();

  if (LatchCmpInst->getOperand(0) == &getFinalIVValue())
    Pred = ICmpInst::getSwappedPredicate(Pred);

  // Need to flip strictness of the predicate when the latch compare instruction
  // is not using StepInst
  if (LatchCmpInst->getOperand(0) == &getStepInst() ||
      LatchCmpInst->getOperand(1) == &getStepInst())
    return Pred;

  // Cannot flip strictness of NE and EQ
  if (Pred != ICmpInst::ICMP_NE && Pred != ICmpInst::ICMP_EQ)
    return ICmpInst::getFlippedStrictnessPredicate(Pred);

  Direction D = getDirection();
  if (D == Direction::Increasing)
    return ICmpInst::ICMP_SLT;

  if (D == Direction::Decreasing)
    return ICmpInst::ICMP_SGT;

  // If cannot determine the direction, then unable to find the canonical
  // predicate
  return ICmpInst::BAD_ICMP_PREDICATE;
}

Direction Loop::LoopBounds::getDirection() const {
  if (const SCEVAddRecExpr *StepAddRecExpr =
          dyn_cast<SCEVAddRecExpr>(SE.getSCEV(&getStepInst())))
    if (const SCEV *StepRecur = StepAddRecExpr->getStepRecurrence(SE)) {
      if (SE.isKnownPositive(StepRecur))
        return Direction::Increasing;
      if (SE.isKnownNegative(StepRecur))
        return Direction::Decreasing;
    }

  return Direction::Unknown;
}

Optional<Loop::LoopBounds> Loop::getBounds(ScalarEvolution &SE) const {
  if (PHINode *IndVar = getInductionVariable(SE))
    return LoopBounds::getBounds(*this, *IndVar, SE);

  return None;
}

PHINode *Loop::getInductionVariable(ScalarEvolution &SE) const {
  if (!isLoopSimplifyForm())
    return nullptr;

  BasicBlock *Header = getHeader();
  assert(Header && "Expected a valid loop header");
  ICmpInst *CmpInst = getLatchCmpInst();
  if (!CmpInst)
    return nullptr;

  Value *LatchCmpOp0 = CmpInst->getOperand(0);
  Value *LatchCmpOp1 = CmpInst->getOperand(1);

  for (PHINode &IndVar : Header->phis()) {
    InductionDescriptor IndDesc;
    if (!InductionDescriptor::isInductionPHI(&IndVar, this, &SE, IndDesc))
      continue;

    BasicBlock *Latch = getLoopLatch();
    Value *StepInst = IndVar.getIncomingValueForBlock(Latch);

    // case 1:
    // IndVar = phi[{InitialValue, preheader}, {StepInst, latch}]
    // StepInst = IndVar + step
    // cmp = StepInst < FinalValue
    if (StepInst == LatchCmpOp0 || StepInst == LatchCmpOp1)
      return &IndVar;

    // case 2:
    // IndVar = phi[{InitialValue, preheader}, {StepInst, latch}]
    // StepInst = IndVar + step
    // cmp = IndVar < FinalValue
    if (&IndVar == LatchCmpOp0 || &IndVar == LatchCmpOp1)
      return &IndVar;
  }

  return nullptr;
}

bool Loop::getInductionDescriptor(ScalarEvolution &SE,
                                  InductionDescriptor &IndDesc) const {
  if (PHINode *IndVar = getInductionVariable(SE))
    return InductionDescriptor::isInductionPHI(IndVar, this, &SE, IndDesc);

  return false;
}

bool Loop::isAuxiliaryInductionVariable(PHINode &AuxIndVar,
                                        ScalarEvolution &SE) const {
  // Located in the loop header
  BasicBlock *Header = getHeader();
  if (AuxIndVar.getParent() != Header)
    return false;

  // No uses outside of the loop
  for (User *U : AuxIndVar.users())
    if (const Instruction *I = dyn_cast<Instruction>(U))
      if (!contains(I))
        return false;

  InductionDescriptor IndDesc;
  if (!InductionDescriptor::isInductionPHI(&AuxIndVar, this, &SE, IndDesc))
    return false;

  // The step instruction opcode should be add or sub.
  if (IndDesc.getInductionOpcode() != Instruction::Add &&
      IndDesc.getInductionOpcode() != Instruction::Sub)
    return false;

  // Incremented by a loop invariant step for each loop iteration
  return SE.isLoopInvariant(IndDesc.getStep(), this);
}

BranchInst *Loop::getLoopGuardBranch() const {
  if (!isLoopSimplifyForm())
    return nullptr;

  BasicBlock *Preheader = getLoopPreheader();
  assert(Preheader && getLoopLatch() &&
         "Expecting a loop with valid preheader and latch");

  // Loop should be in rotate form.
  if (!isRotatedForm())
    return nullptr;

  // Disallow loops with more than one unique exit block, as we do not verify
  // that GuardOtherSucc post dominates all exit blocks.
  BasicBlock *ExitFromLatch = getUniqueExitBlock();
  if (!ExitFromLatch)
    return nullptr;

  BasicBlock *GuardBB = Preheader->getUniquePredecessor();
  if (!GuardBB)
    return nullptr;

  assert(GuardBB->getTerminator() && "Expecting valid guard terminator");

  BranchInst *GuardBI = dyn_cast<BranchInst>(GuardBB->getTerminator());
  if (!GuardBI || GuardBI->isUnconditional())
    return nullptr;

  BasicBlock *GuardOtherSucc = (GuardBI->getSuccessor(0) == Preheader)
                                   ? GuardBI->getSuccessor(1)
                                   : GuardBI->getSuccessor(0);

  // Check if ExitFromLatch (or any BasicBlock which is an empty unique
  // successor of ExitFromLatch) is equal to GuardOtherSucc. If
  // skipEmptyBlockUntil returns GuardOtherSucc, then the guard branch for the
  // loop is GuardBI (return GuardBI), otherwise return nullptr.
  if (&LoopNest::skipEmptyBlockUntil(ExitFromLatch, GuardOtherSucc,
                                     /*CheckUniquePred=*/true) ==
      GuardOtherSucc)
    return GuardBI;
  else
    return nullptr;
}

bool Loop::isCanonical(ScalarEvolution &SE) const {
  InductionDescriptor IndDesc;
  if (!getInductionDescriptor(SE, IndDesc))
    return false;

  ConstantInt *Init = dyn_cast_or_null<ConstantInt>(IndDesc.getStartValue());
  if (!Init || !Init->isZero())
    return false;

  if (IndDesc.getInductionOpcode() != Instruction::Add)
    return false;

  ConstantInt *Step = IndDesc.getConstIntStepValue();
  if (!Step || !Step->isOne())
    return false;

  return true;
}

// Check that 'BB' doesn't have any uses outside of the 'L'
static bool isBlockInLCSSAForm(const Loop &L, const BasicBlock &BB,
                               const DominatorTree &DT,
                               SmallPtrSetImpl<BasicBlock *> &TaskExits) {
  for (const Instruction &I : BB) {
    // Tokens can't be used in PHI nodes and live-out tokens prevent loop
    // optimizations, so for the purposes of considered LCSSA form, we
    // can ignore them.
    if (I.getType()->isTokenTy())
      continue;

    for (const Use &U : I.uses()) {
      const Instruction *UI = cast<Instruction>(U.getUser());
      const BasicBlock *UserBB = UI->getParent();

      // For practical purposes, we consider that the use in a PHI
      // occurs in the respective predecessor block. For more info,
      // see the `phi` doc in LangRef and the LCSSA doc.
      if (const PHINode *P = dyn_cast<PHINode>(UI))
        UserBB = P->getIncomingBlock(U);

      // Check the current block, as a fast-path, before checking whether
      // the use is anywhere in the loop.  Most values are used in the same
      // block they are defined in.  Also, blocks not reachable from the
      // entry are special; uses in them don't need to go through PHIs.
      if (UserBB != &BB && !L.contains(UserBB) && !TaskExits.count(UserBB) &&
          DT.isReachableFromEntry(UserBB))
        return false;
    }
  }
  return true;
}

bool Loop::isLCSSAForm(const DominatorTree &DT) const {
  // For each block we check that it doesn't have any uses outside of this loop.
  SmallPtrSet<BasicBlock *, 4> TaskExits;
  getTaskExits(TaskExits);
  return all_of(this->blocks(), [&](const BasicBlock *BB) {
    return isBlockInLCSSAForm(*this, *BB, DT, TaskExits);
  });
}

bool Loop::isRecursivelyLCSSAForm(const DominatorTree &DT,
                                  const LoopInfo &LI) const {
  // For each block we check that it doesn't have any uses outside of its
  // innermost loop. This process will transitively guarantee that the current
  // loop and all of the nested loops are in LCSSA form.
  SmallPtrSet<BasicBlock *, 4> TaskExits;
  getTaskExits(TaskExits);
  return all_of(this->blocks(), [&](const BasicBlock *BB) {
    return isBlockInLCSSAForm(*LI.getLoopFor(BB), *BB, DT, TaskExits);
  });
}

bool Loop::isLoopSimplifyForm() const {
  // Normal-form loops have a preheader, a single backedge, and all of their
  // exits have all their predecessors inside the loop.
  return getLoopPreheader() && getLoopLatch() && hasDedicatedExits();
}

// Routines that reform the loop CFG and split edges often fail on indirectbr.
bool Loop::isSafeToClone() const {
  // Return false if any loop blocks contain indirectbrs, or there are any calls
  // to noduplicate functions.
  // FIXME: it should be ok to clone CallBrInst's if we correctly update the
  // operand list to reflect the newly cloned labels.
  for (BasicBlock *BB : this->blocks()) {
    if (isa<IndirectBrInst>(BB->getTerminator()) ||
        isa<CallBrInst>(BB->getTerminator()))
      return false;
    if (isa<MultiRetCallInst>(BB->getTerminator()))
      return false;

    for (Instruction &I : *BB)
      if (auto *CB = dyn_cast<CallBase>(&I))
        if (CB->cannotDuplicate())
          return false;
  }
  return true;
}

MDNode *Loop::getLoopID() const {
  MDNode *LoopID = nullptr;

  // Go through the latch blocks and check the terminator for the metadata.
  SmallVector<BasicBlock *, 4> LatchesBlocks;
  getLoopLatches(LatchesBlocks);
  for (BasicBlock *BB : LatchesBlocks) {
    Instruction *TI = BB->getTerminator();
    MDNode *MD = TI->getMetadata(LLVMContext::MD_loop);

    if (!MD)
      return nullptr;

    if (!LoopID)
      LoopID = MD;
    else if (MD != LoopID)
      return nullptr;
  }
  if (!LoopID || LoopID->getNumOperands() == 0 ||
      LoopID->getOperand(0) != LoopID)
    return nullptr;
  return LoopID;
}

void Loop::setLoopID(MDNode *LoopID) const {
  assert((!LoopID || LoopID->getNumOperands() > 0) &&
         "Loop ID needs at least one operand");
  assert((!LoopID || LoopID->getOperand(0) == LoopID) &&
         "Loop ID should refer to itself");

  SmallVector<BasicBlock *, 4> LoopLatches;
  getLoopLatches(LoopLatches);
  for (BasicBlock *BB : LoopLatches)
    BB->getTerminator()->setMetadata(LLVMContext::MD_loop, LoopID);
}

void Loop::setLoopAlreadyUnrolled() {
  LLVMContext &Context = getHeader()->getContext();

  MDNode *DisableUnrollMD =
      MDNode::get(Context, MDString::get(Context, "llvm.loop.unroll.disable"));
  MDNode *LoopID = getLoopID();
  MDNode *NewLoopID = makePostTransformationMetadata(
      Context, LoopID, {"llvm.loop.unroll."}, {DisableUnrollMD});
  setLoopID(NewLoopID);
}

void Loop::setLoopMustProgress() {
  LLVMContext &Context = getHeader()->getContext();

  MDNode *MustProgress = findOptionMDForLoop(this, "llvm.loop.mustprogress");

  if (MustProgress)
    return;

  MDNode *MustProgressMD =
      MDNode::get(Context, MDString::get(Context, "llvm.loop.mustprogress"));
  MDNode *LoopID = getLoopID();
  MDNode *NewLoopID =
      makePostTransformationMetadata(Context, LoopID, {}, {MustProgressMD});
  setLoopID(NewLoopID);
}

void Loop::setDerivedFromTapirLoop() {
  LLVMContext &Context = getHeader()->getContext();

  MDNode *FromTapir = findOptionMDForLoop(this, "llvm.loop.fromtapirloop");

  if (FromTapir)
    return;

  MDNode *FromTapirMD =
      MDNode::get(Context, MDString::get(Context, "llvm.loop.fromtapirloop"));
  MDNode *LoopID = getLoopID();
  MDNode *NewLoopID =
      makePostTransformationMetadata(Context, LoopID, {}, {FromTapirMD});
  setLoopID(NewLoopID);
}

bool Loop::wasDerivedFromTapirLoop() const {
  MDNode *FromTapir = findOptionMDForLoop(this, "llvm.loop.fromtapirloop");

  if (FromTapir)
    return true;

  return false;
}

bool Loop::isAnnotatedParallel() const {
  MDNode *DesiredLoopIdMetadata = getLoopID();

  if (!DesiredLoopIdMetadata)
    return false;

  MDNode *ParallelAccesses =
      findOptionMDForLoop(this, "llvm.loop.parallel_accesses");
  SmallPtrSet<MDNode *, 4>
      ParallelAccessGroups; // For scalable 'contains' check.
  if (ParallelAccesses) {
    for (const MDOperand &MD : drop_begin(ParallelAccesses->operands())) {
      MDNode *AccGroup = cast<MDNode>(MD.get());
      assert(isValidAsAccessGroup(AccGroup) &&
             "List item must be an access group");
      ParallelAccessGroups.insert(AccGroup);
    }
  }

  // The loop branch contains the parallel loop metadata. In order to ensure
  // that any parallel-loop-unaware optimization pass hasn't added loop-carried
  // dependencies (thus converted the loop back to a sequential loop), check
  // that all the memory instructions in the loop belong to an access group that
  // is parallel to this loop.
  for (BasicBlock *BB : this->blocks()) {
    for (Instruction &I : *BB) {
      if (!I.mayReadOrWriteMemory())
        continue;

      if (MDNode *AccessGroup = I.getMetadata(LLVMContext::MD_access_group)) {
        auto ContainsAccessGroup = [&ParallelAccessGroups](MDNode *AG) -> bool {
          if (AG->getNumOperands() == 0) {
            assert(isValidAsAccessGroup(AG) && "Item must be an access group");
            return ParallelAccessGroups.count(AG);
          }

          for (const MDOperand &AccessListItem : AG->operands()) {
            MDNode *AccGroup = cast<MDNode>(AccessListItem.get());
            assert(isValidAsAccessGroup(AccGroup) &&
                   "List item must be an access group");
            if (ParallelAccessGroups.count(AccGroup))
              return true;
          }
          return false;
        };

        if (ContainsAccessGroup(AccessGroup))
          continue;
      }

      // The memory instruction can refer to the loop identifier metadata
      // directly or indirectly through another list metadata (in case of
      // nested parallel loops). The loop identifier metadata refers to
      // itself so we can check both cases with the same routine.
      MDNode *LoopIdMD =
          I.getMetadata(LLVMContext::MD_mem_parallel_loop_access);

      if (!LoopIdMD)
        return false;

      if (!llvm::is_contained(LoopIdMD->operands(), DesiredLoopIdMetadata))
        return false;
    }
  }
  return true;
}

DebugLoc Loop::getStartLoc() const { return getLocRange().getStart(); }

Loop::LocRange Loop::getLocRange() const {
  // If we have a debug location in the loop ID, then use it.
  if (MDNode *LoopID = getLoopID()) {
    DebugLoc Start;
    // We use the first DebugLoc in the header as the start location of the loop
    // and if there is a second DebugLoc in the header we use it as end location
    // of the loop.
    for (unsigned i = 1, ie = LoopID->getNumOperands(); i < ie; ++i) {
      if (DILocation *L = dyn_cast<DILocation>(LoopID->getOperand(i))) {
        if (!Start)
          Start = DebugLoc(L);
        else
          return LocRange(Start, DebugLoc(L));
      }
    }

    if (Start)
      return LocRange(Start);
  }

  // Try the pre-header first.
  if (BasicBlock *PHeadBB = getLoopPreheader())
    if (DebugLoc DL = PHeadBB->getTerminator()->getDebugLoc())
      return LocRange(DL);

  // If we have no pre-header or there are no instructions with debug
  // info in it, try the header.
  if (BasicBlock *HeadBB = getHeader())
    return LocRange(HeadBB->getTerminator()->getDebugLoc());

  return LocRange();
}

#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
LLVM_DUMP_METHOD void Loop::dump() const { print(dbgs()); }

LLVM_DUMP_METHOD void Loop::dumpVerbose() const {
  print(dbgs(), /*Verbose=*/true);
}
#endif

//===----------------------------------------------------------------------===//
// UnloopUpdater implementation
//

namespace {
/// Find the new parent loop for all blocks within the "unloop" whose last
/// backedges has just been removed.
class UnloopUpdater {
  Loop &Unloop;
  LoopInfo *LI;

  LoopBlocksDFS DFS;

  // Map unloop's immediate subloops to their nearest reachable parents. Nested
  // loops within these subloops will not change parents. However, an immediate
  // subloop's new parent will be the nearest loop reachable from either its own
  // exits *or* any of its nested loop's exits.
  DenseMap<Loop *, Loop *> SubloopParents;

  // Flag the presence of an irreducible backedge whose destination is a block
  // directly contained by the original unloop.
  bool FoundIB = false;

public:
  UnloopUpdater(Loop *UL, LoopInfo *LInfo) : Unloop(*UL), LI(LInfo), DFS(UL) {}

  void updateBlockParents();

  void removeBlocksFromAncestors();

  void updateSubloopParents();

protected:
  Loop *getNearestLoop(BasicBlock *BB, Loop *BBLoop);
};
} // end anonymous namespace

/// Update the parent loop for all blocks that are directly contained within the
/// original "unloop".
void UnloopUpdater::updateBlockParents() {
  if (Unloop.getNumBlocks()) {
    // Perform a post order CFG traversal of all blocks within this loop,
    // propagating the nearest loop from successors to predecessors.
    LoopBlocksTraversal Traversal(DFS, LI);
    for (BasicBlock *POI : Traversal) {

      Loop *L = LI->getLoopFor(POI);
      Loop *NL = getNearestLoop(POI, L);

      if (NL != L) {
        // For reducible loops, NL is now an ancestor of Unloop.
        assert((NL != &Unloop && (!NL || NL->contains(&Unloop))) &&
               "uninitialized successor");
        LI->changeLoopFor(POI, NL);
      } else {
        // Or the current block is part of a subloop, in which case its parent
        // is unchanged.
        assert((FoundIB || Unloop.contains(L)) && "uninitialized successor");
      }
    }
  }
  // Each irreducible loop within the unloop induces a round of iteration using
  // the DFS result cached by Traversal.
  bool Changed = FoundIB;
  for (unsigned NIters = 0; Changed; ++NIters) {
    assert(NIters < Unloop.getNumBlocks() && "runaway iterative algorithm");

    // Iterate over the postorder list of blocks, propagating the nearest loop
    // from successors to predecessors as before.
    Changed = false;
    for (LoopBlocksDFS::POIterator POI = DFS.beginPostorder(),
                                   POE = DFS.endPostorder();
         POI != POE; ++POI) {

      Loop *L = LI->getLoopFor(*POI);
      Loop *NL = getNearestLoop(*POI, L);
      if (NL != L) {
        assert(NL != &Unloop && (!NL || NL->contains(&Unloop)) &&
               "uninitialized successor");
        LI->changeLoopFor(*POI, NL);
        Changed = true;
      }
    }
  }
}

/// Remove unloop's blocks from all ancestors below their new parents.
void UnloopUpdater::removeBlocksFromAncestors() {
  // Remove all unloop's blocks (including those in nested subloops) from
  // ancestors below the new parent loop.
  for (BasicBlock *BB : Unloop.blocks()) {
    Loop *OuterParent = LI->getLoopFor(BB);
    if (Unloop.contains(OuterParent)) {
      while (OuterParent->getParentLoop() != &Unloop)
        OuterParent = OuterParent->getParentLoop();
      OuterParent = SubloopParents[OuterParent];
    }
    // Remove blocks from former Ancestors except Unloop itself which will be
    // deleted.
    for (Loop *OldParent = Unloop.getParentLoop(); OldParent != OuterParent;
         OldParent = OldParent->getParentLoop()) {
      assert(OldParent && "new loop is not an ancestor of the original");
      OldParent->removeBlockFromLoop(BB);
    }
  }
}

/// Update the parent loop for all subloops directly nested within unloop.
void UnloopUpdater::updateSubloopParents() {
  while (!Unloop.isInnermost()) {
    Loop *Subloop = *std::prev(Unloop.end());
    Unloop.removeChildLoop(std::prev(Unloop.end()));

    assert(SubloopParents.count(Subloop) && "DFS failed to visit subloop");
    if (Loop *Parent = SubloopParents[Subloop])
      Parent->addChildLoop(Subloop);
    else
      LI->addTopLevelLoop(Subloop);
  }
}

/// Return the nearest parent loop among this block's successors. If a successor
/// is a subloop header, consider its parent to be the nearest parent of the
/// subloop's exits.
///
/// For subloop blocks, simply update SubloopParents and return NULL.
Loop *UnloopUpdater::getNearestLoop(BasicBlock *BB, Loop *BBLoop) {

  // Initially for blocks directly contained by Unloop, NearLoop == Unloop and
  // is considered uninitialized.
  Loop *NearLoop = BBLoop;

  Loop *Subloop = nullptr;
  if (NearLoop != &Unloop && Unloop.contains(NearLoop)) {
    Subloop = NearLoop;
    // Find the subloop ancestor that is directly contained within Unloop.
    while (Subloop->getParentLoop() != &Unloop) {
      Subloop = Subloop->getParentLoop();
      assert(Subloop && "subloop is not an ancestor of the original loop");
    }
    // Get the current nearest parent of the Subloop exits, initially Unloop.
    NearLoop = SubloopParents.insert({Subloop, &Unloop}).first->second;
  }

  succ_iterator I = succ_begin(BB), E = succ_end(BB);
  if (I == E) {
    assert(!Subloop && "subloop blocks must have a successor");
    NearLoop = nullptr; // unloop blocks may now exit the function.
  }
  for (; I != E; ++I) {
    if (*I == BB)
      continue; // self loops are uninteresting

    Loop *L = LI->getLoopFor(*I);
    if (L == &Unloop) {
      // This successor has not been processed. This path must lead to an
      // irreducible backedge.
      assert((FoundIB || !DFS.hasPostorder(*I)) && "should have seen IB");
      FoundIB = true;
    }
    if (L != &Unloop && Unloop.contains(L)) {
      // Successor is in a subloop.
      if (Subloop)
        continue; // Branching within subloops. Ignore it.

      // BB branches from the original into a subloop header.
      assert(L->getParentLoop() == &Unloop && "cannot skip into nested loops");

      // Get the current nearest parent of the Subloop's exits.
      L = SubloopParents[L];
      // L could be Unloop if the only exit was an irreducible backedge.
    }
    if (L == &Unloop) {
      continue;
    }
    // Handle critical edges from Unloop into a sibling loop.
    if (L && !L->contains(&Unloop)) {
      L = L->getParentLoop();
    }
    // Remember the nearest parent loop among successors or subloop exits.
    if (NearLoop == &Unloop || !NearLoop || NearLoop->contains(L))
      NearLoop = L;
  }
  if (Subloop) {
    SubloopParents[Subloop] = NearLoop;
    return BBLoop;
  }
  return NearLoop;
}

LoopInfo::LoopInfo(const DomTreeBase<BasicBlock> &DomTree) { analyze(DomTree); }

bool LoopInfo::invalidate(Function &F, const PreservedAnalyses &PA,
                          FunctionAnalysisManager::Invalidator &) {
  // Check whether the analysis, all analyses on functions, or the function's
  // CFG have been preserved.
  auto PAC = PA.getChecker<LoopAnalysis>();
  return !(PAC.preserved() || PAC.preservedSet<AllAnalysesOn<Function>>() ||
           PAC.preservedSet<CFGAnalyses>());
}

void LoopInfo::erase(Loop *Unloop) {
  assert(!Unloop->isInvalid() && "Loop has already been erased!");

  auto InvalidateOnExit = make_scope_exit([&]() { destroy(Unloop); });

  // First handle the special case of no parent loop to simplify the algorithm.
  if (Unloop->isOutermost()) {
    // Since BBLoop had no parent, Unloop blocks are no longer in a loop.
    for (BasicBlock *BB : Unloop->blocks()) {
      // Don't reparent blocks in subloops.
      if (getLoopFor(BB) != Unloop)
        continue;

      // Blocks no longer have a parent but are still referenced by Unloop until
      // the Unloop object is deleted.
      changeLoopFor(BB, nullptr);
    }

    // Remove the loop from the top-level LoopInfo object.
    for (iterator I = begin();; ++I) {
      assert(I != end() && "Couldn't find loop");
      if (*I == Unloop) {
        removeLoop(I);
        break;
      }
    }

    // Move all of the subloops to the top-level.
    while (!Unloop->isInnermost())
      addTopLevelLoop(Unloop->removeChildLoop(std::prev(Unloop->end())));

    return;
  }

  // Update the parent loop for all blocks within the loop. Blocks within
  // subloops will not change parents.
  UnloopUpdater Updater(Unloop, this);
  Updater.updateBlockParents();

  // Remove blocks from former ancestor loops.
  Updater.removeBlocksFromAncestors();

  // Add direct subloops as children in their new parent loop.
  Updater.updateSubloopParents();

  // Remove unloop from its parent loop.
  Loop *ParentLoop = Unloop->getParentLoop();
  for (Loop::iterator I = ParentLoop->begin();; ++I) {
    assert(I != ParentLoop->end() && "Couldn't find loop");
    if (*I == Unloop) {
      ParentLoop->removeChildLoop(I);
      break;
    }
  }
}

bool
LoopInfo::wouldBeOutOfLoopUseRequiringLCSSA(const Value *V,
                                            const BasicBlock *ExitBB) const {
  if (V->getType()->isTokenTy())
    // We can't form PHIs of token type, so the definition of LCSSA excludes
    // values of that type.
    return false;

  const Instruction *I = dyn_cast<Instruction>(V);
  if (!I)
    return false;
  const Loop *L = getLoopFor(I->getParent());
  if (!L)
    return false;
  if (L->contains(ExitBB))
    // Could be an exit bb of a subloop and contained in defining loop
    return false;

  // We found a (new) out-of-loop use location, for a value defined in-loop.
  // (Note that because of LCSSA, we don't have to account for values defined
  // in sibling loops.  Such values will have LCSSA phis of their own in the
  // common parent loop.)
  return true;
}

AnalysisKey LoopAnalysis::Key;

LoopInfo LoopAnalysis::run(Function &F, FunctionAnalysisManager &AM) {
  // FIXME: Currently we create a LoopInfo from scratch for every function.
  // This may prove to be too wasteful due to deallocating and re-allocating
  // memory each time for the underlying map and vector datastructures. At some
  // point it may prove worthwhile to use a freelist and recycle LoopInfo
  // objects. I don't want to add that kind of complexity until the scope of
  // the problem is better understood.
  LoopInfo LI;
  LI.analyze(AM.getResult<DominatorTreeAnalysis>(F));
  return LI;
}

PreservedAnalyses LoopPrinterPass::run(Function &F,
                                       FunctionAnalysisManager &AM) {
  AM.getResult<LoopAnalysis>(F).print(OS);
  return PreservedAnalyses::all();
}

void llvm::printLoop(Loop &L, raw_ostream &OS, const std::string &Banner) {

  if (forcePrintModuleIR()) {
    // handling -print-module-scope
    OS << Banner << " (loop: ";
    L.getHeader()->printAsOperand(OS, false);
    OS << ")\n";

    // printing whole module
    OS << *L.getHeader()->getModule();
    return;
  }

  OS << Banner;

  auto *PreHeader = L.getLoopPreheader();
  if (PreHeader) {
    OS << "\n; Preheader:";
    PreHeader->print(OS);
    OS << "\n; Loop:";
  }

  for (auto *Block : L.blocks())
    if (Block)
      Block->print(OS);
    else
      OS << "Printing <null> block";

  SmallVector<BasicBlock *, 8> ExitBlocks;
  L.getExitBlocks(ExitBlocks);
  if (!ExitBlocks.empty()) {
    OS << "\n; Exit blocks";
    for (auto *Block : ExitBlocks)
      if (Block)
        Block->print(OS);
      else
        OS << "Printing <null> block";
  }
}

MDNode *llvm::findOptionMDForLoopID(MDNode *LoopID, StringRef Name) {
  // No loop metadata node, no loop properties.
  if (!LoopID)
    return nullptr;

  // First operand should refer to the metadata node itself, for legacy reasons.
  assert(LoopID->getNumOperands() > 0 && "requires at least one operand");
  assert(LoopID->getOperand(0) == LoopID && "invalid loop id");

  // Iterate over the metdata node operands and look for MDString metadata.
  for (unsigned i = 1, e = LoopID->getNumOperands(); i < e; ++i) {
    MDNode *MD = dyn_cast<MDNode>(LoopID->getOperand(i));
    if (!MD || MD->getNumOperands() < 1)
      continue;
    MDString *S = dyn_cast<MDString>(MD->getOperand(0));
    if (!S)
      continue;
    // Return the operand node if MDString holds expected metadata.
    if (Name.equals(S->getString()))
      return MD;
  }

  // Loop property not found.
  return nullptr;
}

MDNode *llvm::findOptionMDForLoop(const Loop *TheLoop, StringRef Name) {
  return findOptionMDForLoopID(TheLoop->getLoopID(), Name);
}

/// Find string metadata for loop
///
/// If it has a value (e.g. {"llvm.distribute", 1} return the value as an
/// operand or null otherwise.  If the string metadata is not found return
/// Optional's not-a-value.
Optional<const MDOperand *> llvm::findStringMetadataForLoop(const Loop *TheLoop,
                                                            StringRef Name) {
  MDNode *MD = findOptionMDForLoop(TheLoop, Name);
  if (!MD)
    return None;
  switch (MD->getNumOperands()) {
  case 1:
    return nullptr;
  case 2:
    return &MD->getOperand(1);
  default:
    llvm_unreachable("loop metadata has 0 or 1 operand");
  }
}

Optional<bool> llvm::getOptionalBoolLoopAttribute(const Loop *TheLoop,
                                                  StringRef Name) {
  MDNode *MD = findOptionMDForLoop(TheLoop, Name);
  if (!MD)
    return None;
  switch (MD->getNumOperands()) {
  case 1:
    // When the value is absent it is interpreted as 'attribute set'.
    return true;
  case 2:
    if (ConstantInt *IntMD =
            mdconst::extract_or_null<ConstantInt>(MD->getOperand(1).get()))
      return IntMD->getZExtValue();
    return true;
  }
  llvm_unreachable("unexpected number of options");
}

bool llvm::getBooleanLoopAttribute(const Loop *TheLoop, StringRef Name) {
  return getOptionalBoolLoopAttribute(TheLoop, Name).getValueOr(false);
}

llvm::Optional<int> llvm::getOptionalIntLoopAttribute(const Loop *TheLoop,
                                                      StringRef Name) {
  const MDOperand *AttrMD =
      findStringMetadataForLoop(TheLoop, Name).getValueOr(nullptr);
  if (!AttrMD)
    return None;

  ConstantInt *IntMD = mdconst::extract_or_null<ConstantInt>(AttrMD->get());
  if (!IntMD)
    return None;

  return IntMD->getSExtValue();
}

int llvm::getIntLoopAttribute(const Loop *TheLoop, StringRef Name,
                              int Default) {
  return getOptionalIntLoopAttribute(TheLoop, Name).getValueOr(Default);
}

bool llvm::isFinite(const Loop *L) {
  return L->getHeader()->getParent()->willReturn();
}

static const char *LLVMLoopMustProgress = "llvm.loop.mustprogress";

bool llvm::hasMustProgress(const Loop *L) {
  return getBooleanLoopAttribute(L, LLVMLoopMustProgress);
}

bool llvm::isMustProgress(const Loop *L) {
  return L->getHeader()->getParent()->mustProgress() || hasMustProgress(L);
}

bool llvm::isValidAsAccessGroup(MDNode *Node) {
  return Node->getNumOperands() == 0 && Node->isDistinct();
}

MDNode *llvm::makePostTransformationMetadata(LLVMContext &Context,
                                             MDNode *OrigLoopID,
                                             ArrayRef<StringRef> RemovePrefixes,
                                             ArrayRef<MDNode *> AddAttrs) {
  // First remove any existing loop metadata related to this transformation.
  SmallVector<Metadata *, 4> MDs;

  // Reserve first location for self reference to the LoopID metadata node.
  MDs.push_back(nullptr);

  // Remove metadata for the transformation that has been applied or that became
  // outdated.
  if (OrigLoopID) {
    for (unsigned i = 1, ie = OrigLoopID->getNumOperands(); i < ie; ++i) {
      bool IsVectorMetadata = false;
      Metadata *Op = OrigLoopID->getOperand(i);
      if (MDNode *MD = dyn_cast<MDNode>(Op)) {
        const MDString *S = dyn_cast<MDString>(MD->getOperand(0));
        if (S)
          IsVectorMetadata =
              llvm::any_of(RemovePrefixes, [S](StringRef Prefix) -> bool {
                return S->getString().startswith(Prefix);
              });
      }
      if (!IsVectorMetadata)
        MDs.push_back(Op);
    }
  }

  // Add metadata to avoid reapplying a transformation, such as
  // llvm.loop.unroll.disable and llvm.loop.isvectorized.
  MDs.append(AddAttrs.begin(), AddAttrs.end());

  MDNode *NewLoopID = MDNode::getDistinct(Context, MDs);
  // Replace the temporary node with a self-reference.
  NewLoopID->replaceOperandWith(0, NewLoopID);
  return NewLoopID;
}

//===----------------------------------------------------------------------===//
// LoopInfo implementation
//

LoopInfoWrapperPass::LoopInfoWrapperPass() : FunctionPass(ID) {
  initializeLoopInfoWrapperPassPass(*PassRegistry::getPassRegistry());
}

char LoopInfoWrapperPass::ID = 0;
INITIALIZE_PASS_BEGIN(LoopInfoWrapperPass, "loops", "Natural Loop Information",
                      true, true)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(LoopInfoWrapperPass, "loops", "Natural Loop Information",
                    true, true)

bool LoopInfoWrapperPass::runOnFunction(Function &) {
  releaseMemory();
  LI.analyze(getAnalysis<DominatorTreeWrapperPass>().getDomTree());
  return false;
}

void LoopInfoWrapperPass::verifyAnalysis() const {
  // LoopInfoWrapperPass is a FunctionPass, but verifying every loop in the
  // function each time verifyAnalysis is called is very expensive. The
  // -verify-loop-info option can enable this. In order to perform some
  // checking by default, LoopPass has been taught to call verifyLoop manually
  // during loop pass sequences.
  if (VerifyLoopInfo) {
    auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    LI.verify(DT);
  }
}

void LoopInfoWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequiredTransitive<DominatorTreeWrapperPass>();
}

void LoopInfoWrapperPass::print(raw_ostream &OS, const Module *) const {
  LI.print(OS);
}

PreservedAnalyses LoopVerifierPass::run(Function &F,
                                        FunctionAnalysisManager &AM) {
  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  auto &DT = AM.getResult<DominatorTreeAnalysis>(F);
  LI.verify(DT);
  return PreservedAnalyses::all();
}

//===----------------------------------------------------------------------===//
// LoopBlocksDFS implementation
//

/// Traverse the loop blocks and store the DFS result.
/// Useful for clients that just want the final DFS result and don't need to
/// visit blocks during the initial traversal.
void LoopBlocksDFS::perform(LoopInfo *LI) {
  LoopBlocksTraversal Traversal(*this, LI);
  for (LoopBlocksTraversal::POTIterator POI = Traversal.begin(),
                                        POE = Traversal.end();
       POI != POE; ++POI)
    ;
}
