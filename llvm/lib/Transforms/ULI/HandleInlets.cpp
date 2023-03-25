/* HandleInlets function pass
 * Turn inlet attributes into inlet psuedoinstructions
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
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/Transforms/ULI/HandleInlets.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#define SV_NAME "uli-handleinlets"
#define DEBUG_TYPE "ULI"


using namespace llvm;

namespace {
    struct HandleInlets : public FunctionPass {

        static char ID; // Pass identification

        HandleInlets() : FunctionPass(ID) {
        }

        virtual bool doInitialization(Module &M) override {
            return Impl.runInitialization(M);
        }

        bool runOnFunction(Function &F) override {
            return Impl.runImpl(F);

        }

    private:
        HandleInletsPass Impl;

    };

}

bool HandleInletsPass::handlePotentialJump(BasicBlock &BB) {
  for (auto it = BB.begin(); it != BB.end(); ++it) {
    auto &instr = *it;
    auto call = dyn_cast<CallInst>(&instr);
    if (!call) continue;
    auto fn = call->getCalledFunction();
    if (!fn) continue;
    if (fn->getIntrinsicID() != Intrinsic::x86_uli_potential_jump) continue;
    auto afterPotentialJump = it; afterPotentialJump++;

    auto BA = dyn_cast<BlockAddress>(call->getArgOperand(0));
    assert(BA);
    auto InletBlock = BA->getBasicBlock();


    it->eraseFromParent();
    auto afterBB = BB.splitBasicBlock(afterPotentialJump);

    auto terminator = BB.getTerminator();

    auto OpaqueTrueTy = FunctionType::get(BoolTy, false);
    auto OpaqueTrue = InlineAsm::get(OpaqueTrueTy, "xor $0, $0",  "=r,~{dirflag},~{fpsr},~{flags}", false);

    auto cond = CallInst::Create(OpaqueTrue, "", terminator);

    auto branch = BranchInst::Create(InletBlock, afterBB, cond);
    branch->setMetadata(LLVMContext::MD_prof, MDBuilder(branch->getContext()).createBranchWeights(1, 99));

    ReplaceInstWithInst(terminator, branch);

    handlePotentialJump(*afterBB);
    return true;
  }
  return false;
}

bool HandleInletsPass::runInitialization(Module &M) {
    auto &C = M.getContext();
    BoolTy = Type::getInt1Ty(C);
    return true;
}

bool HandleInletsPass::runImpl(Function &F) {
    bool changed = false;
    for (auto &BB : F) {
        changed |= handlePotentialJump(BB);
    }
    return changed;
}

PreservedAnalyses
HandleInletsPass::run(Function &F, FunctionAnalysisManager &AM) {

    // Run on function.
    bool Changed = runImpl(F);
    if (!Changed)
        return PreservedAnalyses::all();

    PreservedAnalyses PA;
    // TODO: what analyses are preserved?
    return PA;
}



/////////////////////////////////////////////////////////////

char HandleInlets::ID = 0;
static RegisterPass<HandleInlets> X("handleinlets", "Uli Inlets Pass");


Pass *llvm::createHandleInletsPass() {
    return new HandleInlets();
}
