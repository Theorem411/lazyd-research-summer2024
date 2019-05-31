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

bool HandleInletsPass::runInitialization(Module &M) {
    return true;
}

bool HandleInletsPass::runImpl(Function &F) {
    bool changed = false;

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
