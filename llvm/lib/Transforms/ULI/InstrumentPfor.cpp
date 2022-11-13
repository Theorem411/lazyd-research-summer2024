//===- InstrumentPfor.cpp - Instrument pfor header  -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass attempts to store the next iteration in a local memory
//
//===----------------------------------------------------------------------===//


#include "llvm/Transforms/ULI/InstrumentPfor.h"

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "instrumentpfor"

namespace {  
  struct InstrumentPfor : public FunctionPass {
    /// Pass identification, replacement for type id.
    static char ID;

    /// \brief Construct and initialize pass.
    explicit InstrumentPfor() : FunctionPass(ID) {
    }

    /// \return If we change anything in function \p F.
    virtual bool runOnFunction(Function &F) override {
      // Get required analysis.
      auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
      auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
      return Impl.runImpl(F, SE, LI);
    }

    /// \brief Specify required analysis and preserve analysis that is not
    /// affected by this pass.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<LoopInfoWrapperPass>();
      AU.addRequired<ScalarEvolutionWrapperPass>();
      AU.setPreservesCFG();
    }

  private:
    /// Real implementation.
    InstrumentPforPass Impl;
  };
}

namespace {

  // Copied from LoopInterchange.cpp
  static PHINode *getInductionVariable(Loop *L, ScalarEvolution *SE) {    
    PHINode *InnerIndexVar = L->getCanonicalInductionVariable();
    if (InnerIndexVar)
      return InnerIndexVar;
    if (L->getLoopLatch() == nullptr || L->getLoopPredecessor() == nullptr)
      return nullptr;
    for (BasicBlock::iterator I = L->getHeader()->begin(); isa<PHINode>(I); ++I) {
      PHINode *PhiVar = cast<PHINode>(I);
      Type *PhiTy = PhiVar->getType();
      outs() << "Phi: " << *PhiVar << "\n";
      if (!PhiTy->isIntegerTy() && !PhiTy->isFloatingPointTy() &&
          !PhiTy->isPointerTy()) {
	outs() << "Type not interger, float, or pointer\n";
	return nullptr;
      }

      auto scevExpr = SE->getSCEV(PhiVar);
      assert(scevExpr);
      scevExpr->dump();
      const SCEVAddRecExpr *AddRec =  dyn_cast<SCEVAddRecExpr>(scevExpr);
      if (!AddRec || !AddRec->isAffine()) {
	if(!AddRec)  {
	  outs() << "AddRec == null\n";
	  continue;
	}
	
	if(!AddRec->isAffine()) 	 
	  outs() << "AddRec not affine\n";

	continue;
      }
      const SCEV *Step = AddRec->getStepRecurrence(*SE);
      if (!isa<SCEVConstant>(Step)) {
	outs() << "Not constant\n";
	continue;
      }
      // Found the induction variable.
      // FIXME: Handle loops with more than one induction variable. Note that,
      // currently, legality makes sure we have only one induction variable.
      return PhiVar;
    }
    return nullptr;
  }

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


  bool detachExists(Function& F) {
    for (auto &BB : F) {
      for (auto it = BB.begin(); it != BB.end(); ++it) {
	auto &instr = *it;
	  
	if(isa<DetachInst>(&instr)) {
	  return true;
	}
      }
    }
    return false;
  }  
  
}

void InstrumentPforPass::instrumentLoop(Function &F, ScalarEvolution& SE, Loop* L) {
  auto M = F.getParent();
  const DataLayout &DL = M->getDataLayout();
  LLVMContext& C = M->getContext();

  BasicBlock *Header = L->getHeader();
  BasicBlock *Preheader = L->getLoopPreheader();
  BasicBlock *Latch = L->getLoopLatch();

  const SCEV *Limit = SE.getExitCount(L, Latch);
  outs() << "LS Loop limit: " << *Limit << "\n";

  PHINode *CanonicalIV = getInductionVariable(L, &SE);//Exp.getOrInsertCanonicalInductionVariable(L, CanonicalIVTy);
  assert(CanonicalIV && "Canonical Ind. variable cannot be nulled\n");

  outs() << "Induction variable: " << *CanonicalIV <<"\n";

  const SCEVAddRecExpr *PNSCEV = dyn_cast<const SCEVAddRecExpr>(SE.getSCEV(CanonicalIV));
  auto constStep = dyn_cast<SCEVConstant>(PNSCEV->getStepRecurrence(SE));
  assert(constStep && "Recurrence step must be constant");
  outs() << "Step: " << *constStep << "\n";

  IRBuilder<> B (Header->getFirstNonPHIOrDbgOrLifetime());

  unsigned loc = 0;
  for (Function::const_arg_iterator J = F.arg_begin(); J != F.arg_end(); ++J) {
    // If argument is sret, skip
    if(J->getType()->isPointerTy() && !J->hasStructRetAttr()){
      break;
    }
    loc++;
  }

  Function::arg_iterator args = F.arg_begin() + loc;
  Value* argsCtx = &*args; 

  args = F.arg_begin();
  Value* argsStart = &*args; 

  GlobalVariable* guiOn = GetGlobalVariable("uiOn", TypeBuilder<char, false>::get(C), *M, true);
  Value* ONE = B.getInt8(1);
  Value* ZERO = B.getInt8(0);  

 //#define UI_REGION
#ifdef UI_REGION
  B.CreateCall(ui_disable_region);
#endif

#define NO_UNWIND_POLLPFOR
#ifdef NO_UNWIND_POLLPFOR
  auto nextIteration = B.CreateAdd(CanonicalIV, constStep->getValue());

  // If iv starts at zero, add the first argument (start variable)
  if(PNSCEV->getStart()->isZero()) 
    nextIteration = B.CreateAdd(nextIteration, argsStart);


  B.CreateStore(nextIteration, argsCtx, true);


#else
  Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_unwind_poll_pfor);
  B.CreateCall(pollFcn, {CanonicalIV ,constStep->getValue(), argsCtx});

#endif

#ifdef UI_REGION
  B.CreateCall(ui_enable_region);
#endif

  B.CreateStore(nextIteration, argsCtx, true);
  //B.CreateStore(ONE, guiOn, true);

  B.SetInsertPoint(Preheader->getFirstNonPHIOrDbgOrLifetime());
  //B.CreateStore(ZERO, guiOn, true);

  //B.SetInsertPoint(Preheader->getFirstNonPHIOrDbgOrLifetime());
  B.SetInsertPoint(Latch->getFirstNonPHIOrDbgOrLifetime());

#if 1
  //B.SetInsertPoint(Preheader->getFirstNonPHIOrDbgOrLifetime());
  B.SetInsertPoint(Latch->getTerminator());
  GlobalVariable* prequestcell = GetGlobalVariable("request_cell", ArrayType::get(IntegerType::getInt64Ty(C), 32), *M, true);
  Value* L_ONE = B.getInt64(1);
  auto workExists = B.CreateConstInBoundsGEP2_64(prequestcell, 0, 1 );
  B.CreateStore(L_ONE, workExists);
#endif

}


bool InstrumentPforPass::runImpl(Function &F, ScalarEvolution& SE, LoopInfo& LI)  {
  auto M = F.getParent();
  const DataLayout &DL = M->getDataLayout();
  LLVMContext& C = M->getContext();

  GlobalVariable* prequestcell = GetGlobalVariable("request_cell", ArrayType::get(IntegerType::getInt64Ty(C), 32), *M, true);
  IRBuilder<> B(F.getContext());
  Value* L_ONE = B.getInt64(1);
  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // If Detach exists, set request_cell[0] to 1
  bool bDetachExists= detachExists(F);
  //if(bDetachExists || F.getFnAttribute("poll-at-loop").getValueAsString()=="true") {
  if(bDetachExists) {
    B.SetInsertPoint(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());
    auto workExists = B.CreateConstInBoundsGEP2_64(prequestcell, 0, 1 );
    B.CreateStore(L_ONE, workExists);
  } 

  if(!(F.getFnAttribute("poll-at-loop").getValueAsString()=="true")) return false;

  outs() << "Analyzed function: " << F.getName() << "\n";
  for (Loop *L : LI) {
    SmallVector<Loop *, 8> VisitStack = {L};

    instrumentLoop(F, SE, L);
#if 0
    while (!VisitStack.empty()) {
      Loop *CurrentLoop = VisitStack.pop_back_val();
      auto &SubLoops    = CurrentLoop->getSubLoops();

      if (!SubLoops.empty()) {
	for (Loop *SubLoop : SubLoops)
	  VisitStack.push_back(SubLoop);
      } else {
	instrumentLoop(F, SE, CurrentLoop);
      }
    }
#endif

  }
  return true;
}



PreservedAnalyses InstrumentPforPass::run(Function &F,
					      FunctionAnalysisManager &AM) {
  // Get required analysis.
  auto &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  auto &LI = AM.getResult<LoopAnalysis>(F);

  // Run on function.
  bool Changed = runImpl(F, SE, LI);
  if (!Changed)
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserve<LoopAnalysis>();
  PA.preserveSet<CFGAnalyses>();
  return PA;
}


char InstrumentPfor::ID = 0;

static const char lv_name[] = "LazyD store the next iteration in the header of the loop";

Pass *llvm::createInstrumentPforPass() {
  return new InstrumentPfor();
}
