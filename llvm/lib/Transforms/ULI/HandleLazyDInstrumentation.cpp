/*
 *
 * HandleLazyDInstrumentation function pass that lowers LazyD Instrumentation
 *
 */

#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/Transforms/ULI/HandleLazyDInstrumentation.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#define SV_NAME "uli-handlelazydintrinsics"
#define DEBUG_TYPE "ULI"

using namespace llvm;

namespace {
  struct HandleLazyDInstrumentation : public FunctionPass {

    static char ID; // Pass identification
    HandleLazyDInstrumentation() : FunctionPass(ID) {
    }

    virtual bool doInitialization(Module &M) override {
      return Impl.runInitialization(M);
    }

    bool runOnFunction(Function &F) override {
      doInitialization(*F.getParent());
      return Impl.runImpl(F);
    }

  private:
    HandleLazyDInstrumentationPass Impl;

  };
}


bool HandleLazyDInstrumentationPass::handleLazyDInstrumentation(Function &F) {
  Module *M = F.getParent();
  LLVMContext &ctx = F.getContext();
  IRBuilder<> builder(ctx);
  bool Changed = false;

  // iteration variables
  CallInst *CI = nullptr;
  Function *Intrinsic = nullptr;

  // LLVM Types constructors
  IntegerType *I32 = IntegerType::getInt32Ty(ctx);
  IntegerType *I64 = IntegerType::getInt64Ty(ctx);
  Type *I8Ptr = PointerType::get(Type::getInt8Ty(ctx), 0);
  FunctionType *FnTy = FunctionType::get(
                                         /*Result*/Type::getVoidTy(ctx),
                                         /*Params*/{I8Ptr, I64, I64, I32},
                                         /*isVarArg*/false
                                         );
  PointerType *FnPtrTy = PointerType::get(FnTy, 0);

  Value *idx_zero = ConstantInt::get(Type::getInt64Ty(ctx), 0);

  // file and line number using DISubprogram of parent function F
  DISubprogram *Subprogram = F.getSubprogram();

  // collect list of __builtin_uli_lazyd_inst intrinsic for replacement
  SmallVector<Instruction *, 8> Builtin_Uli_Lazyd_Insts;
  for (auto I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    if ((CI = dyn_cast<CallInst>(&*I))
        && (Intrinsic = CI->getCalledFunction())
        && (Intrinsic->getIntrinsicID() == Intrinsic::uli_lazyd_inst))
      {
	// If no subprogram or the second argument is not a nullptr
	Constant *Message= dyn_cast<Constant>(CI->getArgOperand(1));
	assert(Message && "Message is not a constant");
	if(Message->isNullValue()){
	  errs() << "Messsage: is null\n";
	} else {
	  errs() << "Message is not null\n";
	}

	if (Subprogram) {
	  StringRef subpNameStr = Subprogram->getName();
	  // outs() << "found __builtin_uli_lazyd_inst callsite in " << F.getName() << '\n';
	  builder.SetInsertPoint(&*I);
	  // Extract lazydIntrumentLoop function
	  // %0 = bitcast i8* %fnptr to void (i8*, i64, i64, i32)*
	  Value *FnPtr= CI->getArgOperand(0);
	  assert(FnPtr && "fail to retrieve lazydIntrumentLoop from __builtin_uli_lazyd_inst first arg!");
	  Value *Callee = builder.CreateBitCast(
						/*Value*/FnPtr,
						/*DestTy*/FnPtrTy,
						/*Twine:Name*/"instloop"
						);
	  GlobalVariable *globvar = builder.CreateGlobalString(
							       subpNameStr,
							       "file_and_line_number",
							       0 /* Default AddressSpace */,
							       nullptr /* Default Module */
							       );

	  Value *FileAndLineNumber = builder.CreateInBoundsGEP(
							       /*Ty*/globvar->getValueType(),
							       /*Ptr*/globvar,
							       /*IdxList*/{idx_zero, idx_zero}
							       );

	  // extract other operands of __builtin_uli_lazyd_inst
	  Value *TripCount = CI->getArgOperand(2);
	  Value *GranSize = CI->getArgOperand(3);
	  Value *Depth = CI->getArgOperand(4);
	  assert(FileAndLineNumber
		 && TripCount
		 && GranSize
		 && Depth
		 && "__builtin_uli_lazyd_inst has null argument!");

	  // call void %0(i8* file_and_line_number, i64 trip_count, i64 grain_size, i32 depth)
	  auto res = builder.CreateCall(
			     /*FTy*/FnTy,
			     /*Callee*/Callee,
			     /*Args*/{FileAndLineNumber, TripCount, GranSize, Depth}
			     );

	  res->setDebugLoc(CI->getDebugLoc());
	  res->dump();
	  //res->addFnAttr(Attribute::NoInline);
	}
	// delete original intrinsic later
	Builtin_Uli_Lazyd_Insts.push_back(&*I);
	Changed = true;
      }
  }
  // delete replaced intrinsics
  for (auto *I : Builtin_Uli_Lazyd_Insts) {
    I->eraseFromParent();
  }
  return Changed;
}

bool HandleLazyDInstrumentationPass::runInitialization(Module &M) {
  return true;
}

bool HandleLazyDInstrumentationPass::runImpl(Function &F) {
  bool changed = false;
  changed = handleLazyDInstrumentation(F);
  return changed;
}

PreservedAnalyses
HandleLazyDInstrumentationPass::run(Function &F, FunctionAnalysisManager &AM) {

  runInitialization(*F.getParent());
  // Run on function.
  bool Changed = runImpl(F);
  if (!Changed)
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  // TODO: what analyses are preserved?
  return PA;
}



/////////////////////////////////////////////////////////////

char HandleLazyDInstrumentation::ID = 0;
static RegisterPass<HandleLazyDInstrumentation> X("handlelazydintrumentation", "Handle LazyD Instrumentation");


Pass *llvm::createHandleLazyDInstrumentationPass() {
  return new HandleLazyDInstrumentation();
}
