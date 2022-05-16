//===- ULIPollingInsertion.cpp - Emulate ULI intrinsics -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass inserts ULI message polling before code segments that would take
// long execution time.
//
//===----------------------------------------------------------------------===//


#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/ULI/ULIPollingInsertion.h"

using namespace llvm;

#define SV_NAME "uli-pollinsert"
#define DEBUG_TYPE "ULI"

// Do not add the polling instrumentation
static cl::opt<bool> DisableUnwindPoll(
                                       "disable-unwind-polling2", cl::init(false), cl::NotHidden,
                                       cl::desc("Do not insert any polling call (default = off)"));


// Polling at prologue, epilogue, and inner loop
static cl::opt<int> EnableProperPolling(
                                        "enable-proper-polling2", cl::init(0), cl::NotHidden,
                                        cl::desc("Enable polling at prologue, epilogue, and inner loop (default = 0)"));


namespace {

/// The ULI polling insertion pass (legacy)
struct ULIPollingInsertion : public FunctionPass {

  /// Pass identification, replacement for type id.
  static char ID;

  /// \brief Construct and initialize pass.
  explicit ULIPollingInsertion() : FunctionPass(ID) {
  }

  /// \return If we change anything in function \p F.
  virtual bool runOnFunction(Function &F) override {
    // Get required analysis.
    auto *DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    auto *LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

    return Impl.runImpl(F, DT, LI);
  }

  /// \brief Specify required analysis and preserve analysis that is not
  /// affected by this pass.
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.setPreservesCFG();
  }

private:
  /// Real implementation.
  ULIPollingInsertionPass Impl;
};

} // end anonymous namespace

bool ULIPollingInsertionPass::insertPollingAtFunction(Function &F) {
  // Insert at the exits of function.
  const BasicBlock &EntryBlock = F.getEntryBlock();
  for (BasicBlock &BB : F) {
    // Exit blocks should not have successor and are reachable.
    if (std::distance(succ_begin(&BB), succ_end(&BB)) == 0 &&
        isPotentiallyReachable(&EntryBlock, &BB, DT, LI)) {
      Instruction *InsertPos = BB.getTerminator();
      CallInst::Create(PollingFunc, PollingArgs, "", InsertPos);
    }
  }
  return true;
}

#if 0
bool ULIPollingInsertionPass::insertPollingAtLoop(Loop &L) {
  // Only insert at the inner most loop. Do DFS on nested loop.
  bool Changed = false;
  SmallVector<Loop *, 8> VisitStack = {&L};
  while (!VisitStack.empty()) {
    Loop *CurrentLoop = VisitStack.pop_back_val();
    auto &SubLoops    = CurrentLoop->getSubLoops();

    if (!SubLoops.empty()) {
      // Not inner most loop, continue exploring its sub-loops.
      for (Loop *SubLoop : SubLoops)
        VisitStack.push_back(SubLoop);
    } else {
      // Inner most loop, insert ULI polling.
      BasicBlock *HeaderBlock = CurrentLoop->getHeader();
      if (HeaderBlock) {
        Instruction *InsertPos = HeaderBlock->getTerminator();
        CallInst::Create(PollingFunc, PollingArgs, "", InsertPos);
        Changed = true;
      }
    }
  }

  return Changed;
}

#else


bool ULIPollingInsertionPass::instrumentLoop (Loop& L) {
  Function *F = L.getHeader()->getParent();
  Module *M = F->getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(M->getContext());

  // Inner most loop, insert ULI polling.
  BasicBlock *HeaderBlock = L.getHeader();
  if (HeaderBlock) {
    B.SetInsertPoint(HeaderBlock->getFirstNonPHIOrDbgOrLifetime());
    Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_unwind_poll);
    B.CreateCall(pollFcn);
    DEBUG(dbgs() << F->getName() << ": Polling at outer most loop\n");
  }
  return true;
}


bool ULIPollingInsertionPass::insertPollingAtLoop(Loop &L) {
  SmallVector<Loop *, 8> VisitStack = {&L};
  Function *F = L.getHeader()->getParent();
  
  bool Changed = false;

  instrumentLoop(L);

  while (!VisitStack.empty()) {
    Loop *CurrentLoop = VisitStack.pop_back_val();
    auto &SubLoops    = CurrentLoop->getSubLoops();

    if (!SubLoops.empty()) {
#if 1
      for (Loop *SubLoop : SubLoops)
	VisitStack.push_back(SubLoop);
#endif
    } else {
      //instrumentLoop(F, CurrentLoop, bHaveUnwindAlloc);
    }
  }

  return Changed;
}


#endif

bool ULIPollingInsertionPass::runImpl(Function &F,
                                      DominatorTree *DT_,
                                      LoopInfo *LI_) {
  // Get required analysis.
  DT = DT_;
  LI = LI_;

  // FIXME: Don't poll yet
  return false;

#if 0
  // Skip functions that do not require ULI polling.
  if (isNoPollingFunction(F))
    return false;

  // Insert polling at the beginning of function and loops.
  Module &M = *F.getParent();
  initializePollingFunction(M);
  insertPollingAtFunction(F);
  for (Loop *L : *LI)
    insertPollingAtLoop(*L);
#else  
  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // Instrument prologue and epilogue to insert parallel runtime call  
  IRBuilder<> B(F.getContext());
  B.SetInsertPoint(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());
  Module *M = F.getParent();

  // Insert poling
  // Polling @prologue
  if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
    Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_unwind_poll);
    auto res = B.CreateCall(pollFcn);
    DEBUG(dbgs() << F.getName() << " : Polling at prologue\n");
  }

  // Polling @epilogue
  for (auto &BB : F){
    Instruction * termInst = BB.getTerminator();
    if(isa<ReturnInst>(termInst) ){
      B.SetInsertPoint(termInst);

      if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
	Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_unwind_poll);
	if(EnableProperPolling >= 1 ) {
	  auto res = B.CreateCall(pollFcn);
	  //res->setTailCall(true);
	  DEBUG(dbgs() << F.getName() << " : Polling at epilogue\n");
	}
      }
    }
  }

  // Polling @loop
  if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
    // Insert Poll in looping
    for (auto *L : *LI) {
      // Only insert at the inner most loop. Do DFS on nested loop.
      if(EnableProperPolling >= 2 || F.getFnAttribute("poll-at-loop").getValueAsString()=="true") {
	insertPollingAtLoop(*L);
      }
    }
  }
#endif
  return true;
}

PreservedAnalyses ULIPollingInsertionPass::run(Function &F,
                                               FunctionAnalysisManager &AM) {
  // Get required analysis.
  auto *DT = &AM.getResult<DominatorTreeAnalysis>(F);
  auto *LI = &AM.getResult<LoopAnalysis>(F);

  // Run on function.
  bool Changed = runImpl(F, DT, LI);
  if (!Changed)
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserve<LoopAnalysis>();
  PA.preserveSet<CFGAnalyses>();
  return PA;
}

char ULIPollingInsertion::ID = 0;

static const char lv_name[] = "ULI polling insertion";

Pass *llvm::createULIPollingInsertionPass() {
  return new ULIPollingInsertion();
}
