#include "llvm-c/Core.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/PassRegistry.h"
#include "llvm/Transforms/ULI/SendUli.h"

using namespace llvm;

#define SV_NAME "uli-senduli-replyuli"
#define DEBUG_TYPE "ULI"

const int uliargindex_send = 0;
const int uliargindex_reply = 16;

namespace {
  struct SendUli : public FunctionPass {

    static char ID; // Pass identification

    explicit SendUli() : FunctionPass(ID) {
    }

  public:
    bool runOnFunction(Function &F) override {

      return Impl.runImpl(F);

    } // end function decl

  private:
    /// Real implementation.
    SendUliPass Impl;

  };
}
////////////////////////////////////////////////////////////////
void SendUliPass::showargs(const char* which, const CallInst *call_inst, Value* numargs) {
  return;
  errs() << "===========\n" << which << ": " << *call_inst << "\n" <<
    "NumOps:" << call_inst->arg_size() << " as " << *numargs << "\n";
  for (unsigned int i = 0; i < call_inst->arg_size(); i++) {
    Value* v = call_inst->getArgOperand(i);
    errs() << i << ": " << *v << "\n";
  }
  errs() << "===========\n";
}



Value * SendUliPass::handleArgs(Value * v, IRBuilder<>& builder, LLVMContext &ctx) {
  Value * zext = nullptr;
  if(v->getType()->isIntegerTy()) {
    // Handle integer
    zext = builder.CreateZExt(v, IntegerType::getInt64Ty(ctx), "t5");
  } else if(v->getType()->isFloatingPointTy()) {
    // Handle floating point
    // Sort of "hack"-ed, there should be a better way

    // Int64 * tmp_var
    Value * tmp_var = builder.CreateAlloca(IntegerType::getInt64Ty(ctx)->getPointerTo());
    // double tmp_var2
    Value * tmp_var2 = builder.CreateAlloca(v->getType());
    // tmp_var2 = v (argn)
    builder.CreateStore(v, tmp_var2);
    // tmp_var = &tmp_var2
    Value * ret_bitcast = builder.CreateBitCast(tmp_var2, IntegerType::getInt64Ty(ctx)->getPointerTo());
    builder.CreateStore(ret_bitcast, tmp_var);

    // zext = *tmp_var
    Value* tmp_addr = builder.CreateLoad(IntegerType::getInt64Ty(ctx)->getPointerTo(), tmp_var);
    zext =  builder.CreateLoad(IntegerType::getInt64Ty(ctx), tmp_addr);

  } else if(v->getType()->isPointerTy()){
    // Handle pointer
    zext = builder.CreateCast(Instruction::PtrToInt, v, IntegerType::getInt64Ty(ctx));
  } else {
    v->dump();
    assert(true && "Type of v not supported as ulihandler's argument!");
  }
  return zext;
}
/////////////////////////////////////////////////////////////

bool SendUliPass::runImpl(Function &F) {
  LLVMContext &ctx = F.getContext();
  Module *M = F.getParent();
  IRBuilder<> builder(ctx);
  Function *fn = NULL;
  CallInst *call_inst = NULL;
  uint32_t reg = 0;
  bool changed = false;
  SmallVector<Instruction *,2> del_instrs;

  // Function calls
  Function *send0cN = Intrinsic::getDeclaration(M, Intrinsic::uli_send0cN);
  Function *reply0cN = Intrinsic::getDeclaration(M, Intrinsic::uli_reply0cN);
  Function *toireg = Intrinsic::getDeclaration(M, Intrinsic::uli_toireg);

  // iterate through basic blocks for call instructions
  for (BasicBlock &B : F){
    for(Instruction &I : B){
      call_inst = NULL; fn = NULL; // reset
      // compare called function with uli send intrinsic
      if((call_inst = dyn_cast<CallInst>(&I))
	 && (fn = call_inst->getCalledFunction())
	 && (fn->getIntrinsicID() == Intrinsic::uli_send))
	{
	  //insert the function before matched Instruction, we will delete original uli_send anyways
	  builder.SetInsertPoint(&I);
	  reg =uliargindex_send;

	  // create left shift and xor
	  Value * dest = builder.CreateZExt(call_inst->getArgOperand(0), IntegerType::getInt64Ty(ctx), "t<1");
	  Value * shldest = builder.CreateShl(dest, 32, "t2");
	  Value * num = builder.CreateZExt(call_inst->getArgOperand(1), IntegerType::getInt64Ty(ctx), "t3");
	  Value * dest_and_num = builder.CreateXor(shldest, num, "t4");

	  /*unsigned int n_messages = 0;
	    if (llvm::ConstantInt * CI = dyn_cast<llvm::ConstantInt>(call_inst->getArgOperand(9))) {
	    if(CI->getBitWidth() <= 32)
	    n_messages = CI->getSExtValue();
	    errs() << n_messages << " messages\n";
	    }*/
	  // skip over first 3 args, loop through var args, create uli_toireg call for each arg
	  //						errs() << call_inst->getNumOperands();

	  // Pass the argument of the message to the send register (ulitoireg construction)
	  for (unsigned int i = 3; i < call_inst->getNumOperands()-1; i++){
	    Value * v = call_inst->getArgOperand(i);
	    Value * zext = handleArgs(v, builder, ctx);
	    builder.CreateCall(toireg, { builder.getInt32(reg++), zext });
	  }

	  // create send instruction
	  Value* foo_ptr = call_inst->getArgOperand(2);
	  Value* numargs = builder.getInt32(call_inst->arg_size()-3);
	  builder.CreateCall(send0cN, { dest_and_num , foo_ptr, numargs });
	  showargs("Send", call_inst, numargs);

	  // save instructions to delete in vector, cannot delete in loop
	  del_instrs.push_back(&I);
	  changed = true;
	}
      else if((call_inst = dyn_cast<CallInst>(&I))
	      && (fn = call_inst->getCalledFunction())
	      && (fn->getIntrinsicID() == Intrinsic::uli_reply))
	{

	  //Insert the function before matched Instruction, we will delete original uli_reply anyways
	  builder.SetInsertPoint(&I);
	  reg = uliargindex_reply;

	  // skip over first arg, loop through var args, create uli_toireg call for each arg except last which is number of arguments
	  // Pass the argument of the message to the reply register (ulitoireg construction)
	  for (unsigned int i = 1; i < call_inst->arg_size(); i++) {
	    Value * v = call_inst->getArgOperand(i);
	    Value * zext = handleArgs(v, builder, ctx);
	    builder.CreateCall(toireg, { builder.getInt32(reg++), zext });
	  }

	  // create reply instruction
	  Value* foo_ptr = call_inst->getArgOperand(0);
	  Value* numargs = builder.getInt32(call_inst->arg_size()-1);

	  showargs("REPLY", call_inst, numargs);
	  builder.CreateCall(reply0cN, { foo_ptr, numargs });

	  // save instructions to delete in vector, cannot delete in loop
	  del_instrs.push_back(&I);
	  changed = true;

	}
    } // end bb loop
  } // end fn loop

  for (auto In : del_instrs){
    Instruction& inst = *In;
    inst.eraseFromParent(); // delete instrs
  }

  return changed;
}

PreservedAnalyses
SendUliPass::run(Function &F, FunctionAnalysisManager &AM) {
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

char SendUli::ID = 0;
static RegisterPass<SendUli> X("senduli", "Send Uli Pass");

Pass *llvm::createSendUliPass() {
  return new SendUli();
}
