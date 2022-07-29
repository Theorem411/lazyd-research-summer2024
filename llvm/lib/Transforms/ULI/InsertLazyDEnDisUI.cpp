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


#define DEFAULT_GET_CILKRTS_FUNC(name)                                  \
  static Function *Get__cilkrts_##name(Module& M) {                     \
						   return cast<Function>(M.getOrInsertFunction(	\
											       "__cilkrts_"#name, \
												 TypeBuilder<__cilkrts_##name, false>::get(M.getContext()) \
												 )); \

using overhead_ty = void (void);
DEFAULT_GET_LIB_FUNC(overhead);

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
    return Impl.runImpl(F);
  }

  /// \brief Specify required analysis and preserve analysis that is not
  /// affected by this pass.
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
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

bool InsertLazyDEnDisUIPass::runImpl(Function &F) {
  if( DisableLazyDEnDisUI ) return false;

  Module *M = F.getParent();
  LLVMContext& C = M->getContext();

  // Get the global variable
  GlobalVariable* guiOn = GetGlobalVariable("uiOn", TypeBuilder<char, false>::get(C), *M, true);
  IRBuilder<> B(F.getContext());
  Value* ONE = B.getInt8(1);
  Value* ZERO = B.getInt8(0);  

  auto stui = Intrinsic::getDeclaration(M, Intrinsic::x86_ui_stui);
  auto clui = Intrinsic::getDeclaration(M, Intrinsic::x86_ui_clui);
  
  // Overhead to inflate the cost of storing uiOn
  Constant* OVERHEAD = Get_overhead(*M);

  // Find the fork, detach, reattach inst
  SmallPtrSet<CallInst*, 4> forkCallInsts;
  for (auto& BB: F) {
    if (DetachInst* DI = dyn_cast<DetachInst>(BB.getTerminator())) {
      // Insert clui before detach
      B.SetInsertPoint(DI);
      
      if(EnableStuiClui) {
	B.CreateCall(clui);
      } else {
	B.CreateStore(ZERO, guiOn, true);   
      }
      
      BasicBlock* detachBlock = dyn_cast<DetachInst>(DI)->getDetached();
      for ( Instruction &II : *detachBlock) {
	if( CallInst* CI = dyn_cast<CallInst>(&II) ) {
	  forkCallInsts.insert(CI);
	}
      }
    } else if (ReattachInst* RI = dyn_cast<ReattachInst>(BB.getTerminator())) {
      // Insert stui after reattach
      BasicBlock* contBB = RI->getDetachContinue();
      B.SetInsertPoint(contBB->getFirstNonPHIOrDbgOrLifetime());

      if(EnableStuiClui)
	B.CreateCall(stui);
      else
	B.CreateStore(ONE, guiOn, true);
    }
  }

  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // Instrument prologue and epilogue to insert parallel runtime call  
  B.SetInsertPoint(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

  // Insert enable after prologue and function call
  if(EnableStuiClui)
    B.CreateCall(stui);
  else
    B.CreateStore(ONE, guiOn, true);

  // Insert disable before epilogue and function call
  SmallVector<ReturnInst*, 4> instrumentedRet;
  for (auto &BB : F){
    Instruction * termInst = BB.getTerminator();
    if(isa<ReturnInst>(termInst) ){
      instrumentedRet.push_back(dyn_cast<ReturnInst>(termInst));
    }
  }

  for(auto termInst: instrumentedRet) {
    B.SetInsertPoint(termInst);
    if(EnableStuiClui)
      B.CreateCall(clui);
    else
      B.CreateStore(ZERO, guiOn, true);   
  }

  // Insert disable before epilogue and function call
  SmallVector<CallInst* , 4> instrumentedCall;
  SmallVector<MultiRetCallInst*, 4> instrumentedMrc;
  for (auto &BB : F){
    for(auto &II : BB) {

      if (isa<IntrinsicInst>(&II) || isa<InlineAsm>(&II)) {
	continue;
      }

      if(isa<CallInst>(&II) && forkCallInsts.find(dyn_cast<CallInst>(&II)) == forkCallInsts.end()) {
	instrumentedCall.push_back(dyn_cast<CallInst>(&II));
		
      } else if(isa<InvokeInst>(&II)) {
	assert(0 && "Not supported yet");

      } else if(isa<MultiRetCallInst>(&II)) {
	auto mrc = dyn_cast<MultiRetCallInst>(&II);

	if (isa<IntrinsicInst>(mrc->getCalledFunction()))
	  continue;
	
	//instrumentedMrc.push_back(mrc);
      }
    }
  }

  for(auto ci: instrumentedCall) {
    B.SetInsertPoint(ci);
    if(EnableStuiClui)
      B.CreateCall(clui);
    else
      B.CreateStore(ZERO, guiOn, true);
	
    B.SetInsertPoint(ci->getNextNode());
	
    if(EnableStuiClui)
      B.CreateCall(stui);
    else
      B.CreateStore(ONE, guiOn, true);
  }

  for(auto mrc: instrumentedMrc) {
    B.SetInsertPoint(mrc);
    
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

  return true;
}

PreservedAnalyses InsertLazyDEnDisUIPass::run(Function &F,
                                               FunctionAnalysisManager &AM) {

  // Run on function.
  bool Changed = runImpl(F);
  if (!Changed)
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  return PA;
}

char InsertLazyDEnDisUI::ID = 0;

static const char lv_name[] = "LazyD enable disable UI insertion";

Pass *llvm::createInsertLazyDEnDisUIPass() {
  return new InsertLazyDEnDisUI();
}
