//===- InsertLazyDEnDisUI.cpp - Insert polling for LazyD  -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass insert enable and disable for LazyD. Insert at function prologue, epilogue, before and after function call
//
//===----------------------------------------------------------------------===//


#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/ULI/InsertLazyDEnDisUI.h"

using namespace llvm;

#define SV_NAME "lazyd-endisui"
#define DEBUG_TYPE "lazyd-trans"


// Do not add the polling instrumentation
static cl::opt<bool> DisableLazyDEnDisUI("disable-lazy-endisui", cl::init(false), cl::NotHidden,
                                       cl::desc("Do not insert any polling call (default = off)"));

static cl::opt<bool> EnableStuiClui("enable-lazy-stuiclui", cl::init(false), cl::NotHidden,
                                       cl::desc("Enable/disable UI using stui and clui instead"));


namespace {

/// The ULI polling insertion pass (legacy)
struct InsertLazyDEnDisUI : public FunctionPass {

  /// Pass identification, replacement for type id.
  static char ID;

  /// \brief Construct and initialize pass.
  explicit InsertLazyDEnDisUI() : FunctionPass(ID) {
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
  InsertLazyDEnDisUIPass Impl;
};

} // end anonymous namespace


namespace {

  GlobalVariable* GetGlobalVariable(const char* GlobalName, Type* GlobalType, Module& M, bool localThread=false){
    GlobalVariable* globalVar = M.getNamedGlobal(GlobalName);
    if(globalVar){
      return globalVar;
    }
    globalVar = dyn_cast<GlobalVariable>(M.getOrInsertGlobal(GlobalName, GlobalType));
    globalVar->setLinkage(GlobalValue::ExternalLinkage);
    if(localThread)
      globalVar->setThreadLocal(true);
    return globalVar;
  }
}

bool InsertLazyDEnDisUIPass::runImpl(Function &F,
                                      DominatorTree *DT_,
                                      LoopInfo *LI_) {
  // Get required analysis.
  DT = DT_;
  LI = LI_;

  if( DisableLazyDEnDisUI ) return false;

  Module *M = F.getParent();
  LLVMContext& C = M->getContext();

  // Get the global variable
  GlobalVariable* guiOn = GetGlobalVariable("uiOn", TypeBuilder<char, false>::get(C), *M, true);

  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // Instrument prologue and epilogue to insert parallel runtime call  
  IRBuilder<> B(F.getContext());
  B.SetInsertPoint(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

  Value* ONE = B.getInt8(1);
  Value* ZERO = B.getInt8(0);

  auto clui = Intrinsic::getDeclaration(M, Intrinsic::x86_ui_stui);
  auto stui = Intrinsic::getDeclaration(M, Intrinsic::x86_ui_clui);

  // Insert enable after prologue and function call
  if(EnableStuiClui)
    B.CreateCall(stui);
  else
    B.CreateStore(ONE, guiOn, true);

  // Insert disable before epilogue and function call
  for (auto &BB : F){
    Instruction * termInst = BB.getTerminator();
    if(isa<ReturnInst>(termInst) ){
      B.SetInsertPoint(termInst);
      if(EnableStuiClui)
	B.CreateCall(clui);
      else
	B.CreateStore(ZERO, guiOn, true);
    }
  }

  // Insert disable before epilogue and function call
  for (auto &BB : F){
    for(auto &II : BB) {

      if (isa<IntrinsicInst>(&II) || isa<InlineAsm>(&II)) {
	continue;
      }

      if(isa<CallInst>(&II)) {
	B.SetInsertPoint(&II);
	if(EnableStuiClui)
	  B.CreateCall(clui);
	else
	  B.CreateStore(ZERO, guiOn, true);
	
	B.SetInsertPoint(II.getNextNode());
	
	if(EnableStuiClui)
	  B.CreateCall(stui);
	else
	  B.CreateStore(ONE, guiOn, true);
		
      } else if(isa<InvokeInst>(&II)) {
	assert(0 && "Not supported yet");

      } else if(isa<MultiRetCallInst>(&II)) {
	auto mrc = dyn_cast<MultiRetCallInst>(&II);

	if (isa<IntrinsicInst>(mrc->getCalledFunction()))
	  continue;

	B.SetInsertPoint(&II);
	
	if(EnableStuiClui)
	  B.CreateCall(clui);
	else
	  B.CreateStore(ZERO, guiOn, true);
	
	auto bb0 = mrc->getDefaultDest();

	B.SetInsertPoint(bb0->getFirstNonPHIOrDbgOrLifetime()->getNextNode());	
	
	if(EnableStuiClui)
	  B.CreateCall(stui);
	else
	  B.CreateStore(ONE, guiOn, true);
      }
    }
  }  

  return true;
}

PreservedAnalyses InsertLazyDEnDisUIPass::run(Function &F,
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

char InsertLazyDEnDisUI::ID = 0;

static const char lv_name[] = "LazyD enable disable UI insertion";

Pass *llvm::createInsertLazyDEnDisUIPass() {
  return new InsertLazyDEnDisUI();
}
