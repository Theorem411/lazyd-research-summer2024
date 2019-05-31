/* HandleUli function pass
 * Jennifer Bi
 * Function pass that transforms ulihandlers
 * Creates calls to ulifromireg, and stores data from the register into arguments
 */

#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/ULI/HandleUli.h"

const int uliargindex_reply = 16;

#define SV_NAME "uli-handleuli"
#define DEBUG_TYPE "ULI"


using namespace llvm;

namespace {
  struct HandleUli : public FunctionPass {

    static char ID; // Pass identification

    HandleUli() : FunctionPass(ID) {
    }

    bool runOnFunction(Function &F) override {
      return Impl.runImpl(F);

    } // end runOnFunction

  private:
    HandleUliPass Impl;

  };

}

/////////////////////////////////////////////////////////////

bool HandleUliPass::runImpl(Function &F) {

  Module *M = F.getParent();
  LLVMContext &ctx = F.getContext();
  bool changed = false;
  bool summary_changed = false;
  IRBuilder<> builder(ctx);

  Function *fromireg = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_fromireg);
  unsigned int i = uliargindex_reply;
  Value * ret = nullptr;
  Instruction *I = nullptr;
  // Instruction to delete
  SmallVector<Instruction *,2> del_instrs;

  // check for ulihandler tag
  if (!(F.hasFnAttribute(Attribute::UserLevelInterrupt))) {
    return false;
  }

  // Use to remove badref error, not sure why  builder.SetInsertPoint(I); works
  for (Instruction &instr : F.front()){
    I = &instr;
    break;
  }
  builder.SetInsertPoint(I);


  // loop through arguments to grab argument and use replaceAllUsesWith to set it to the value fromireg
  for (Argument *v = F.arg_begin()+1; v != F.arg_end(); v++){

    ret = nullptr;
    changed=true;

    if(v->getType()->isIntegerTy()){
      // Handle integer
      // Get the content of the argument from ulifromireg
      ret = builder.CreateCall(fromireg, {builder.getInt32(i)});

      // Truncate the type if necessary
      if (!v->getType()->isIntegerTy(64)){
	ret = builder.CreateCast(Instruction::Trunc, ret, v->getType());
      }
    } else if(v->getType()->isFloatingPointTy()) {
      // Handle floating point argument
      // Sort of "hack", there should be a better way to pass the value

      // ret = ulifromireg(i)
      ret = builder.CreateCall(fromireg, {builder.getInt32(i)});

      // Create : float * tmp_var
      Value * tmp_var = builder.CreateAlloca(Type::getDoubleTy(ctx)->getPointerTo());
      // Create : Int64 tmp_var2
      Value * tmp_var2 = builder.CreateAlloca(ret->getType());
      // tmp_var2 = ret
      builder.CreateStore(ret, tmp_var2);

      // tmp_var = &tmp_var2
      Value * ret_bitcast = builder.CreateBitCast(tmp_var2, Type::getDoubleTy(ctx)->getPointerTo());
      builder.CreateStore(ret_bitcast, tmp_var);

      // ret = *tmp_var (get the floating point number)
      Value* tmp_addr = builder.CreateLoad(Type::getDoubleTy(ctx)->getPointerTo(), tmp_var);
      ret =  builder.CreateLoad(Type::getDoubleTy(ctx), tmp_addr);

      if(v->getType() != Type::getDoubleTy(ctx)) {
	ret = builder.CreateCast(Instruction::FPTrunc, ret, v->getType());
      }

    } else if(v->getType()->isPointerTy()) {
      // Handle pointer argument
      ret = builder.CreateCall(fromireg, {builder.getInt32(i)});
      ret = builder.CreateCast(Instruction::IntToPtr, ret, v->getType());
      changed=true;
    } else {
      // Assert if argument passed is not supported by ulifromireg
      v->dump();
      changed=false;
      assert(true && "Type of v not supported as ulihandler's argument!");
    }

    if(changed){
      // Replace the use of the argument (v) with the return value from ulifromireg
      v->replaceAllUsesWith(ret);
      // Increment argument counter
      i++;
    }

    summary_changed |= changed;

  } // end args loop
  return summary_changed;

}

PreservedAnalyses
HandleUliPass::run(Function &F, FunctionAnalysisManager &AM) {
  //SCG printf(" %s %s %d\n", __FILE__, __func__, __LINE__);
  // Get required analysis.
  // We need dominator analysis because we need to find valid positions to
  // insert alloca instructions for storing return values of extern calls.


  // Run on function.
  bool Changed = runImpl(F);
  if (!Changed)
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}



/////////////////////////////////////////////////////////////

char HandleUli::ID = 0;
static RegisterPass<HandleUli> X("handleuli", "Uli Handler Pass");

Pass *llvm::createHandleUliPass() {
  return new HandleUli();
}
