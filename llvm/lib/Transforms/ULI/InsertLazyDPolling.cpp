//===- InsertLazyDPolling.cpp - Insert polling for LazyD  -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass insert polling for LazyD. Currently only insert at the function prologue.
//
//===----------------------------------------------------------------------===//


#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/ULI/InsertLazyDPolling.h"

using namespace llvm;

#define SV_NAME "lazyd-pollinsert"
#define DEBUG_TYPE "lazyd-trans"

// Do not add the polling instrumentation
static cl::opt<bool> DisableUnwindPoll("disable-lazy-poll", cl::init(false), cl::NotHidden,
                                       cl::desc("Do not insert any polling call (default = off)"));


// Polling at prologue, epilogue, and inner loop
static cl::opt<int> EnableProperPolling("lazy-poll-freq", cl::init(0), cl::NotHidden,
                                        cl::desc("0: Poll at prologue, 1: Poll at prologue+epilogue, 2: Poll at prologue+epilogue+loop"));


namespace {

/// The ULI polling insertion pass (legacy)
struct InsertLazyDPolling : public FunctionPass {

  /// Pass identification, replacement for type id.
  static char ID;

  /// \brief Construct and initialize pass.
  explicit InsertLazyDPolling() : FunctionPass(ID) {
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
  InsertLazyDPollingPass Impl;
};

} // end anonymous namespace

bool InsertLazyDPollingPass::instrumentLoop (Loop& L) {
  Function *F = L.getHeader()->getParent();
  Module *M = F->getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(M->getContext());

  // Inner most loop, insert ULI polling.
  BasicBlock *HeaderBlock = L.getHeader();
  if (HeaderBlock) {
    B.SetInsertPoint(HeaderBlock->getFirstNonPHIOrDbgOrLifetime());
    Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::uli_unwind_poll);
    B.CreateCall(pollFcn);
    LLVM_DEBUG(dbgs() << F->getName() << ": Polling at outer most loop\n");
  }
  return true;
}


bool InsertLazyDPollingPass::insertPollingAtLoop(Loop &L) {
  SmallVector<Loop *, 8> VisitStack = {&L};
  Function *F = L.getHeader()->getParent();

  bool Changed = false;

  instrumentLoop(L);

  // Still in development, don't use function.
  while (!VisitStack.empty()) {
    Loop *CurrentLoop = VisitStack.pop_back_val();
    auto &SubLoops    = CurrentLoop->getSubLoops();

    if (!SubLoops.empty()) {
      for (Loop *SubLoop : SubLoops)
	VisitStack.push_back(SubLoop);
    }
  }

  return Changed;
}

bool InsertLazyDPollingPass::runImpl(Function &F,
                                      DominatorTree *DT_,
                                      LoopInfo *LI_) {
  // Get required analysis.
  DT = DT_;
  LI = LI_;

  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // Instrument prologue and epilogue to insert parallel runtime call
  IRBuilder<> B(F.getContext());
  B.SetInsertPoint(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());
  Module *M = F.getParent();

  // Insert poling
  // Polling @prologue
  if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
    Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::uli_unwind_poll);
    auto res = B.CreateCall(pollFcn);
    LLVM_DEBUG(dbgs() << F.getName() << " : Polling at prologue\n");
  }

  // Polling @epilogue
  for (auto &BB : F){
    Instruction * termInst = BB.getTerminator();
    if(isa<ReturnInst>(termInst) ){
      B.SetInsertPoint(termInst);

      if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
	Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::uli_unwind_poll);
	if(EnableProperPolling >= 1 ) {
	  auto res = B.CreateCall(pollFcn);
	  LLVM_DEBUG(dbgs() << F.getName() << " : Polling at epilogue\n");
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
  return true;
}

PreservedAnalyses InsertLazyDPollingPass::run(Function &F,
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

char InsertLazyDPolling::ID = 0;

static const char lv_name[] = "LazyD polling insertion";

Pass *llvm::createInsertLazyDPollingPass() {
  return new InsertLazyDPolling();
}
