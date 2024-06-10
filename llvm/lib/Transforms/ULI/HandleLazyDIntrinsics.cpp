/*
 *
 * HandleLazyDIntrinsics function pass that lowers LazyD Intrinsics
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
#include "llvm/Transforms/ULI/HandleLazyDIntrinsics.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#define SV_NAME "uli-handlelazydintrinsics"
#define DEBUG_TYPE "ULI"

using namespace llvm;

namespace {
  struct HandleLazyDIntrinsics : public FunctionPass {

    static char ID; // Pass identification
    HandleLazyDIntrinsics() : FunctionPass(ID) {
    }

    virtual bool doInitialization(Module &M) override {
      return Impl.runInitialization(M);
    }

    bool runOnFunction(Function &F) override {
      doInitialization(*F.getParent());
      return Impl.runImpl(F);
    }

  private:
    HandleLazyDIntrinsicsPass Impl;

  };
}

/// Handle both changereturnaddress and savereturnaddress
bool HandleLazyDIntrinsicsPass::handleChangeRetAddr(BasicBlock &BB)  {
  // Search for the unwind path entry, if not found, return
  Module* M = BB.getModule();
  Function* F = BB.getParent();
  LLVMContext& C = BB.getContext();
  IRBuilder<> B(C);
  Type *VoidPtrTy  = PointerType::getInt8PtrTy(C);

  SmallVector<Instruction*, 4> inst2delete;
  bool modified = false;
  // Search for the intrinsic related to unwind polling
  for (auto it = BB.begin(); it != BB.end(); ++it) {
    auto &instr = *it;
    auto call = dyn_cast<CallInst>(&instr);
    if (!call) continue;
    auto fn = call->getCalledFunction();
    if (!fn) continue;
    bool isFcnNotChangeRetAddr = (fn->getIntrinsicID() != Intrinsic::uli_change_returnaddress) && ( (fn->getIntrinsicID() != Intrinsic::uli_save_returnaddress));
    if (isFcnNotChangeRetAddr) continue;

    B.SetInsertPoint(&instr);
    modified=true;
    // Collect the intrinsic
    if(fn->getIntrinsicID() == Intrinsic::uli_change_returnaddress) {
      inst2delete.push_back(call);
    } else if(fn->getIntrinsicID() == Intrinsic::uli_save_returnaddress) {
      inst2delete.push_back(call);
    }
  }

  // Modify and delete call to intrisic
  for(auto ii: inst2delete) {
    auto call = dyn_cast<CallInst>(ii);
    auto fn = call->getCalledFunction();
    B.SetInsertPoint(ii);

    if(fn->getIntrinsicID() == Intrinsic::uli_change_returnaddress) {
      auto addrOfRA = Intrinsic::getDeclaration(M, Intrinsic::addressofreturnaddress, {VoidPtrTy});
      Value* myRA = B.CreateCall(addrOfRA);
      myRA = B.CreateBitCast(myRA, IntegerType::getInt64Ty(C)->getPointerTo());
      Value* newAddr = B.CreateCast(Instruction::PtrToInt, call->getArgOperand(0), IntegerType::getInt64Ty(C));
      // Store new returnaddress to location of returnaddress
      B.CreateStore(newAddr, myRA, 1);
    } else if(fn->getIntrinsicID() == Intrinsic::uli_save_returnaddress) {
      auto addrOfRA = Intrinsic::getDeclaration(M, Intrinsic::addressofreturnaddress, {VoidPtrTy});
      Value* myRA = B.CreateCall(addrOfRA);
      myRA = B.CreateBitCast(myRA, IntegerType::getInt64Ty(C)->getPointerTo());
      Value* raValue = B.CreateLoad(IntegerType::getInt64Ty(C), myRA);
      Value* storageLoc = B.CreateBitCast(call->getArgOperand(0), IntegerType::getInt64Ty(C)->getPointerTo());
      // Store return address to stack slot
      B.CreateStore(raValue, storageLoc, 1);
    }

    ii->eraseFromParent();
  }

  return modified;
}

bool HandleLazyDIntrinsicsPass::runInitialization(Module &M) {
  return true;
}

bool HandleLazyDIntrinsicsPass::runImpl(Function &F) {
  bool changed = false;
  for (auto &BB : F) {
    changed |= handleChangeRetAddr(BB);
  }
  return changed;
}

PreservedAnalyses
HandleLazyDIntrinsicsPass::run(Function &F, FunctionAnalysisManager &AM) {

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

char HandleLazyDIntrinsics::ID = 0;
static RegisterPass<HandleLazyDIntrinsics> X("handlelazydintinsics", "Handle LazyD Intrinsics");


Pass *llvm::createHandleLazyDIntrinsicsPass() {
  return new HandleLazyDIntrinsics();
}
