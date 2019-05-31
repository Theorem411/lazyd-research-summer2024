//===- ULIIntrinsicToExternCall.h - Emulate ULI intrinsics ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass replace ULI intrinsics with external calls to the ULI emulation
// library.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_ULI_ULIINTRINSICTOEXTERNCALL_H
#define LLVM_TRANSFORMS_ULI_ULIINTRINSICTOEXTERNCALL_H

#include "llvm/IR/Dominators.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Pass.h"

namespace llvm {

/// The ULI intrinsic to external call pass. (new pass manager)
struct ULIIntrinsicToExternCallPass
    : public PassInfoMixin<ULIIntrinsicToExternCallPass> {

  /// \brief All info required to insert an extern call.
  struct ExternCall {
    Intrinsic::ID ID;  /// The type of intrinsic.
    std::string Name;  /// The extern function name.
    FunctionType *FTy; /// The type of extern function.
    bool SameTy;       /// If the types of intrinsic and extern functions are
                       /// identical.
  };

public:
  /// \return Preserved analyses of function \p F after transformation.
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  /// \return If we rewrite any intrinsic in function \p F.
  bool runImpl(Function &F, DominatorTree *DT_);

private:
  /// LLVM dominator tree.
  DominatorTree *DT = nullptr;

  /// \brief Create the mapping from intrinsic functions to extern functions.
  void initializeIntrinsicExternMap(Module &M);

  /// \brief Rewrite the calling convention of \p F to default C.
  void stripULICallingConvention(Function &F) {
    F.setCallingConv(CallingConv::C);
  }

  /// \brief Insert extern call to ULI return at each return instruction.
  void insertExternReturns(Function &F);

  /// \brief Collect all ULI intrinsic calls in the function \p F.
  void collectIntrinsicCalls(Function &F);

  /// \return The rewritten extern call of \p IntrinsicCI.
  CallInst *rewriteToExternSameType(CallInst *IntrinsicCI,
                                    const ExternCall &Extern,
                                    Module &M);

  /// \return The rewritten extern call of \p IntrinsicCI.
  CallInst *rewriteToExternDiffType(CallInst *IntrinsicCI,
                                    const ExternCall &Extern,
                                    Module &M);

  /// \return If we rewrite any intrinsic call successfully.
  /// Rewrite collected intrinsic calls to extern calls.
  bool rewriteToExtern(ArrayRef<CallInst *> IntrinsicCalls, Module &M);

  /// Map intrinsic functions to the extern function we want to rewrite to.
  SmallDenseMap<Function *, ExternCall> IntrinsicExternMap;

  /// Hold all intrinsic calls to be rewritten in current function.
  SmallVector<CallInst *, 4> IntrinsicCalls;
};

/// \return An instance of created pass for legacy pass manager.
Pass *createULIIntrinsicToExternCallPass();

} // end namespace llvm

#endif // LLVM_TRANSFORMS_ULI_ULIINTRINSICTOEXTERNCALL_H
