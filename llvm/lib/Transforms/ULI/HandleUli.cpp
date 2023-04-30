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

    Function *fromireg = Intrinsic::getDeclaration(M, Intrinsic::uli_fromireg);
    unsigned int i = uliargindex_reply;
    Value * ret = nullptr;
    // Instruction to delete
    SmallVector<Instruction *,2> del_instrs;

    // check for ulihandler tag
    if (!(F.hasFnAttribute(Attribute::UserLevelInterrupt))) {
        return false;
    }

    BasicBlock & bbFront = F.front();
    Instruction & iiFront = bbFront.front();
    builder.SetInsertPoint(&iiFront);


    Argument * arg_end = F.arg_end();
    // The last 3 variable are used for storing the special register
    if(  (F.hasFnAttribute(Attribute::ULINonAtomic)) ){
        arg_end = F.arg_end() - 3;
    }

    // Generated code :
    // ...
    // Prologue
    // ...
    // first param = fromireg (0)
    // second param = fromireg(1)
    // ...
    // ...
    // (if Attr.ULINonAtomic == true) {
    //   // Nothing
    // else {
    //   last param -2 = fromireg(n - 2)
    //   last param -1 = fromireg(n - 1)
    //   last param    = fromireg(n)
    //}

    // loop through arguments to grab argument and use replaceAllUsesWith to set it to the value fromireg
    for (Argument *v = F.arg_begin()+1; v != arg_end; v++){
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

    // ================================= ULI NON ATOMIC ===============================================
    // check for uli_non_atomic tag
    if ( (F.hasFnAttribute(Attribute::ULINonAtomic)) ) {
        // If a nonatomicpass attribute exists, the last three parameters store the special register
        Function *rdulirdi =   Intrinsic::getDeclaration(M, Intrinsic::uli_rdrdi);
        Function *rduliflags = Intrinsic::getDeclaration(M, Intrinsic::uli_rdflags);
        Function *rduliRA = Intrinsic::getDeclaration(M, Intrinsic::uli_rdRA);
        Function *rduliregs[3] = {rdulirdi, rduliflags, rduliRA};

        Function *wrulirdi =   Intrinsic::getDeclaration(M, Intrinsic::uli_wrrdi);
        Function *wruliflags = Intrinsic::getDeclaration(M, Intrinsic::uli_wrflags);
        Function *wruliRA = Intrinsic::getDeclaration(M, Intrinsic::uli_wrRA);
        Function *wruliregs[3] = {wrulirdi, wruliflags, wruliRA};

        Function *uliAtomic =  Intrinsic::getDeclaration(M, Intrinsic::uli_atomic);

        // Insert restoring the uli special register before the prologue and an enable uli atomic before restoring the special register
        BasicBlock & bbBack = F.back();
        Instruction & iiBack = bbBack.back();
        BasicBlock::iterator bIt = builder.GetInsertPoint();
        builder.SetInsertPoint(&iiBack);

        //-------------------------------------------------------------
        // Generated code :
        // ...
        // End user code
        // ...
        // Set recursive uli / interruptable uli / nonatomic uli = false
        // write to uli register rdi (last param - 2)
        // write to uli register flags (last param -1)
        // write to uli register return address (last param)
        // ....
        // Epilogue
        // ...



        builder.CreateCall( uliAtomic,  {builder.getInt64(1)} );

        int ii = 0;
        Argument * v = NULL;
        for (v = F.arg_end()-3; v != F.arg_end(); v++){
            // If parameters is a pointer, then convert it to long unsigned.
            if (v->getType()->isPointerTy()){
                ret = builder.CreateCast(Instruction::PtrToInt, v, Type::getInt64Ty(ctx));
                builder.CreateCall( wruliregs[ii], {ret}   );
            } else {
                builder.CreateCall( wruliregs[ii], {v}   );
            }
            ii++;
        }

        builder.SetInsertPoint(&*bIt);
        //-------------------------------------------------------------


        //-------------------------------------------------------------
        // Generated code :
        // ...
        // Prologue
        // ...
        // first param = fromireg (0)
        // second param = fromireg(1)
        // ...
        // ...
        // last param -2 = read from uli register rdi
        // last param -1 = read from uli register flags
        // last param = read from uli register return address


        ii =0;
        // Similiar to the ulifromireg code
        for (Argument *v = F.arg_end()-3; v != F.arg_end(); v++){
            ret = nullptr;
            changed=true;

            if(v->getType()->isIntegerTy()){
                // Handle integer
                // Get the content of the argument from uli special register
                ret = builder.CreateCall( rduliregs[ii] );

                // Truncate the type if necessary
                if (!v->getType()->isIntegerTy(64)){
                    ret = builder.CreateCast(Instruction::Trunc, ret, v->getType());
                }

            } else if(v->getType()->isFloatingPointTy()) {
                // Handle floating point argument
                // Sort of "hack", there should be a better way to pass the value

                // ret = read from uli special register
                ret = builder.CreateCall( rduliregs[ii] );

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
                ret = builder.CreateCall( rduliregs[ii] );
                ret = builder.CreateCast(Instruction::IntToPtr, ret, v->getType());
                changed=true;
            } else {
                // Assert if argument passed is not supported by read from uli special register
                v->dump();
                changed=false;
                assert(true && "Type of v not supported as ulihandler's argument!");
            }

            if(changed){
                // Replace the use of the argument (v) with the return value from uli special register
                v->replaceAllUsesWith(ret);
            }

            ii++;

            summary_changed |= changed;

        } // end args loop
        //-------------------------------------------------------------

        //-------------------------------------------------------------

        // Generate code :
        // ...
        // Saving uli register to last 3 parameters
        // ...
        // ...
        // Set recursive uli / interruptable uli / nonatomic uli = true
        // ...
        // ...
        // Begin User code
        // ...

        // Insert a disable uli atomic after the uli_rdnextpc instruction
        Function::iterator b = F.begin();
        for (BasicBlock::iterator i = b->begin(); i != b->end(); ++i) {
            CallInst * call_inst = NULL;
            Function * fn = NULL;

            if((call_inst = dyn_cast<CallInst>(i))
               && (fn = call_inst->getCalledFunction())
               && (fn->getIntrinsicID() == Intrinsic::uli_rdRA)){

                builder.SetInsertPoint(i->getNextNode());
                builder.CreateCall( uliAtomic,  {builder.getInt64(0)} );

                break;

            }
        }
        //-------------------------------------------------------------
    }

    return summary_changed;

}


PreservedAnalyses
HandleUliPass::run(Function &F, FunctionAnalysisManager &AM) {
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
