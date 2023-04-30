//===- ULIPollingInsertion.h - Emulate ULI intrinsics ---------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass inserts ULI message polling before code segments that would take
// long execution time.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_ULI_ULIPOLLINGINSERTION_H
#define LLVM_TRANSFORMS_ULI_ULIPOLLINGINSERTION_H

#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Pass.h"

namespace llvm {

/// The ULI polling insertion pass.
struct ULIPollingInsertionPass : public PassInfoMixin<ULIPollingInsertionPass> {

public:
  /// \return Preserved analyses of function \p F after transformation.
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  /// \return If we insert any polling in function \p F.
  bool runImpl(Function &F, DominatorTree *DT_, LoopInfo *LI_);

private:
  /// LLVM dominator tree.
  DominatorTree *DT = nullptr;

  /// LLVM loop info.
  LoopInfo *LI = nullptr;

  /// \return If function \p F does not need ULI polling.
  bool isNoPollingFunction(Function &F) const {
    return F.hasFnAttribute(Attribute::ULINoPolling);
  }

  /// \return Extern function that simulates ULI polling.
  void initializePollingFunction(Module &M) {
    LLVMContext &Ctx  = M.getContext();
    Type *VoidTy      = Type::getVoidTy(Ctx);
    Type *Int32Ty     = Type::getInt32Ty(Ctx);
    Type *Int8PtrTy   = Type::getInt8PtrTy(Ctx);
    FunctionType *FTy = FunctionType::get(VoidTy, {Int32Ty, Int8PtrTy}, false);
    PollingFunc       = M.getOrInsertFunction("POLL", FTy);
    Value *CZero      = ConstantInt::get(Int32Ty, 0);
    Value *CNull      = ConstantPointerNull::get(cast<PointerType>(Int8PtrTy));
    PollingArgs       = {CZero, CNull};
  }

  ///  Add polling in loop
  bool instrumentLoop(Loop& L);

  /// \return If we insert any ULI polling at the entry of function \p F.
  bool insertPollingAtFunction(Function &F);

  /// \return If we insert any ULI polling at the pre-header of loop \p L.
  bool insertPollingAtLoop(Loop &L);

  /// The extern function that simulates ULI polling.
  FunctionCallee PollingFunc = nullptr;

  /// Hold the arguments of polling function.
  SmallVector<Value *, 2> PollingArgs;
};

/// \return An instance of created pass for legacy pass manager.
Pass *createULIPollingInsertionPass();

} // end namespace llvm

#endif // LLVM_TRANSFORMS_ULI_ULIPOLLINGINSERTION_H
