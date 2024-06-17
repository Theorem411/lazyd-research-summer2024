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

static cl::opt<bool> DisableUnwindPoll2(
"lazy-disable-unwind-polling2", cl::init(false), cl::NotHidden,
  cl::desc("Do not insert any polling call (default = off)"));


namespace {
  struct InstrumentPfor : public FunctionPass {
    /// Pass identification, replacement for type id.
    static char ID;

    /// \brief Construct and initialize pass.
    explicit InstrumentPfor() : FunctionPass(ID) {
    }

    virtual bool doInitialization(Module &M) override {
      return Impl.runInitialization(M);
    }

    /// \return If we change anything in function \p F.
    virtual bool runOnFunction(Function &F) override {
      // Get required analysis.
      auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
      auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
      doInitialization(*F.getParent());
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

  // Copied from CilkABI.cpp
  /// Helper methods for storing to and loading from struct fields.
  static Value *GEP(IRBuilder<> &B, Value *Base, int Field) {
    return B.CreateConstInBoundsGEP2_32(
					Base->getType()->getScalarType()->getPointerElementType(), Base, 0,
					Field);

  }

  static unsigned GetAlignment(const DataLayout &DL, StructType *STy, int field) {
    return DL.getPrefTypeAlignment(STy->getElementType(field));
  }

  static void StoreSTyField(IRBuilder<> &B, const DataLayout &DL, StructType *STy,
			    Value *Val, Value *Dst, int Field,
			    bool isVolatile = false,
			    AtomicOrdering Ordering = AtomicOrdering::NotAtomic) {
    StoreInst *S = B.CreateAlignedStore(Val, GEP(B, Dst, Field),
					Align(GetAlignment(DL, STy, Field)), isVolatile);
    S->setOrdering(Ordering);

  }

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
      LLVM_DEBUG(dbgs() << "Phi: " << *PhiVar << "\n");
      if (!PhiTy->isIntegerTy() && !PhiTy->isFloatingPointTy() &&
          !PhiTy->isPointerTy()) {
	LLVM_DEBUG(dbgs() << "Type not interger, float, or pointer\n");
	return nullptr;
      }

      auto scevExpr = SE->getSCEV(PhiVar);
      assert(scevExpr);
      const SCEVAddRecExpr *AddRec =  dyn_cast<SCEVAddRecExpr>(scevExpr);
      if (!AddRec || !AddRec->isAffine()) {
	if(!AddRec) {
	  LLVM_DEBUG(dbgs() << "AddRec == null\n");
	  continue;
	}
	if(!AddRec->isAffine()) {
	  LLVM_DEBUG(dbgs() << "AddRec not affine\n");
	  continue;
	}
      }
      const SCEV *Step = AddRec->getStepRecurrence(*SE);
      if (!isa<SCEVConstant>(Step)) {
	LLVM_DEBUG(dbgs() << "SCEV Not a constant\n");
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

//

/*
  define private fastcc void @foo.outline_pfor.cond.ls1.1par-for-seq(i32 %__begin.0.start.ls1, i32 %end.ls1, i32* align 8 %ivStorage.ls1) unnamed_addr #4 {
  pfor.cond.preheader.ls1:
    br label %pfor.inc.ls1

  pfor.inc.ls1:                                     ; preds = %pfor.inc.ls1, %pfor.cond.preheader.ls1
    %__begin.0.ls1 = phi i32 [ %0, %pfor.inc.ls1 ], [ %__begin.0.start.ls1, %pfor.cond.preheader.ls1 ]
    store i8 1, i8* getelementptr inbounds (%struct._request_channel, %struct._request_channel* @req_local, i64 0, i32 2), align 2
    %0 = add i32 %__begin.0.ls1, 1
    store volatile i32 %0, i32* %ivStorage.ls1, align 8

    //....Loop body..........

    %exitcond.not.ls1 = icmp eq i32 %0, %end.ls1
    br i1 %exitcond.not.ls1, label %pfor.cond.cleanup.ls1, label %pfor.inc.ls1, !llvm.loop !10

  pfor.cond.cleanup.ls1:                            ; preds = %pfor.inc.ls1
    ret void
  }

*/

void InstrumentPforPass::instrumentLoop(Function &F, ScalarEvolution& SE, Loop* L) {
  auto M = F.getParent();
  const DataLayout &DL = M->getDataLayout();
  LLVMContext& C = M->getContext();

  BasicBlock *Header = L->getHeader();
  BasicBlock *Preheader = L->getLoopPreheader();
  BasicBlock *Latch = L->getLoopLatch();

  assert(Header && "Header does not exists");
  //assert(Preheader && "Preheader does not exists");
  assert(Latch && "Latch does not exists");

  // Unused code (for debugging purpose)
  const SCEV *Limit = SE.getExitCount(L, Latch);
  LLVM_DEBUG(dbgs() << "LS Loop limit: " << *Limit << "\n");

  // Get the induction variable
  PHINode *CanonicalIV = getInductionVariable(L, &SE);//Exp.getOrInsertCanonicalInductionVariable(L, CanonicalIVTy);
  assert(CanonicalIV && "Canonical Ind. variable cannot be nulled\n");
  LLVM_DEBUG(dbgs() << "Induction variable: " << *CanonicalIV <<"\n");

  // Get the constant step
  const SCEVAddRecExpr *PNSCEV = dyn_cast<const SCEVAddRecExpr>(SE.getSCEV(CanonicalIV));
  auto constStep = dyn_cast<SCEVConstant>(PNSCEV->getStepRecurrence(SE));
  assert(constStep && "Recurrence step must be constant");
  LLVM_DEBUG(dbgs() << "Step: " << *constStep << "\n");


  // Skip argument of type sret
  IRBuilder<> B (Header->getFirstNonPHIOrDbgOrLifetime());
  unsigned loc = 0;
  for (Function::const_arg_iterator J = F.arg_begin(); J != F.arg_end(); ++J) {
    if(J->getType()->isPointerTy() && !J->hasStructRetAttr()){
      break;
    }
    loc++;
  }

  // Locate the storage to store the next iteration passed from parent to child
  Function::arg_iterator args = F.arg_begin() + loc;
  Value* argsCtx = &*args;
  args = F.arg_begin();
  Value* argsStart = &*args;

  // FIXME: Used for to disable and enable interrupt (currently not used in ULI-PRL)
  GlobalVariable* guiOn = GetGlobalVariable("uiOn", Type::getInt8Ty(C), *M, true);
  Value* ONE = B.getInt8(1);
  Value* ZERO = B.getInt8(0);
  Function* ui_disable_region = Intrinsic::getDeclaration(M, Intrinsic::ui_disable_region);
  Function* ui_enable_region = Intrinsic::getDeclaration(M, Intrinsic::ui_enable_region);

#define NO_UNWIND_POLLPFOR
#ifdef NO_UNWIND_POLLPFOR
  // nextIteration = currentIteration+1
  auto nextIteration = B.CreateAdd(CanonicalIV, constStep->getValue());
  // If iv starts at zero, add the first argument (start variable)
  // May not be needed?
  if(PNSCEV->getStart()->isZero())
    nextIteration = B.CreateAdd(nextIteration, argsStart);
#else
  assert(false && "Currently not working");
  Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_unwind_poll_pfor);
  B.CreateCall(pollFcn, {CanonicalIV ,constStep->getValue(), argsCtx});
#endif

  // Store the next iteration to the ivStorage passed by the parent
  B.CreateStore(nextIteration, argsCtx, true);

  // FIXME: Have not been tested, used to disable the reception of interrupt using a local thread variable
  //B.CreateStore(ONE, guiOn, true);
  //B.SetInsertPoint(Preheader->getFirstNonPHIOrDbgOrLifetime());
  //B.CreateStore(ZERO, guiOn, true);
  //B.SetInsertPoint(Preheader->getFirstNonPHIOrDbgOrLifetime());
  B.SetInsertPoint(Latch->getFirstNonPHIOrDbgOrLifetime());

  // Store potential work at the latch
  GlobalVariable* reqlocal = GetGlobalVariable("req_local", RequestChannelTy, *M, true);
  if(!DisableUnwindPoll2)
    StoreSTyField(B, DL, RequestChannelTy,
		  B.getInt8(1),
		  reqlocal, RequestChannelFields::potentialParallelTask, /*isVolatile=*/false,
		  AtomicOrdering::NotAtomic);

}


bool InstrumentPforPass::runImpl(Function &F, ScalarEvolution& SE, LoopInfo& LI)  {
  auto M = F.getParent();
  const DataLayout &DL = M->getDataLayout();
  LLVMContext& C = M->getContext();

  bool Changed=false;

  GlobalVariable* reqlocal = GetGlobalVariable("req_local", RequestChannelTy, *M, true);
  IRBuilder<> B(F.getContext());
  Value* L_ONE = B.getInt64(1);
  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // If Detach exists, set request_cell[0] to 1
  bool bDetachExists= detachExists(F);
  if(bDetachExists) {
    B.SetInsertPoint(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

    // Store potential parallel task at the beginning of the function if it contains detach
    // Is this needed?
    if(!DisableUnwindPoll2)
      StoreSTyField(B, DL, RequestChannelTy,
		    B.getInt8(1),
		    reqlocal, RequestChannelFields::potentialParallelTask, /*isVolatile=*/false,
		    AtomicOrdering::NotAtomic);
  }

  // If it is a not a parallel-loop.
  if(!(F.getFnAttribute("poll-at-loop").getValueAsString()=="true")) return false;

  LLVM_DEBUG(dbgs() << "Analyzed function: " << F.getName() << "\n");

  // Instrument loop to store next iteration and set potential parallel task
  // Potentially, it can be used to disable and enable UI when using PRL
  for (Loop *L : LI) {
    SmallVector<Loop *, 8> VisitStack = {L};
    instrumentLoop(F, SE, L);
    Changed=true;
  }
  return Changed;
}

bool InstrumentPforPass::runInitialization(Module &M) {
  auto &C = M.getContext();
  initialized = false;

  // Create the structure for request and response channel
  // Copied from CilkABI.cpp
  Type *BoolTy = Type::getInt1Ty(C);
  Type *VoidPtrTy = Type::getInt8PtrTy(C);
  Type *Int64Ty = Type::getInt64Ty(C);
  Type *Int32Ty = Type::getInt32Ty(C);
  Type *Int16Ty = Type::getInt16Ty(C);
  Type *Int8Ty  = Type::getInt8Ty(C);

  // Get or create local definitions of Cilk RTS structure types.
  RequestChannelTy = StructType::lookupOrCreate(C, "struct._request_channel");
  ResponseChannelTy = StructType::lookupOrCreate(C, "struct._response_channel");

  if (RequestChannelTy->isOpaque()) {
    RequestChannelTy->setBody(
			      Int32Ty,                     // senderThreadId
			      ArrayType::get(Int8Ty, 2),   // padding_char
			      Int8Ty,                      // potentialParallelTask
			      Int8Ty,                      // inLoop
			      ArrayType::get(Int64Ty, 31)  // padding
			      );
  }

  if (ResponseChannelTy->isOpaque())
    ResponseChannelTy->setBody(
			       Int32Ty,
			       Int8Ty,
			       Int8Ty,
			       ArrayType::get(Int8Ty, 250)
			       );

  return true;
}


PreservedAnalyses InstrumentPforPass::run(Function &F,
					      FunctionAnalysisManager &AM) {
  // Get required analysis.
  auto &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  auto &LI = AM.getResult<LoopAnalysis>(F);
  runInitialization(*F.getParent());

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
