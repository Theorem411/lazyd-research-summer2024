//===- HandleLazyDIntrinsics.h - Lower LazyD Intrinsics ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass lower LazyD Intrinsics
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_ULI_HANDLELAZYDINTRINSICS_H
#define LLVM_TRANSFORMS_ULI_HANDLELAZYDINTRINSICS_H

#include "llvm/IR/Dominators.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Pass.h"

namespace llvm {

struct HandleLazyDIntrinsicsPass
    : public PassInfoMixin<HandleLazyDIntrinsicsPass> {
  bool handleChangeRetAddr(BasicBlock &BB);

public:
  /// \return Preserved analyses of function \p F after transformation.
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  bool runInitialization(Module &M);
  bool runImpl(Function &F);
};

/// \return An instance of created pass for legacy pass manager.
Pass *createHandleLazyDIntrinsicsPass();

} // end namespace llvm

#endif // LLVM_TRANSFORMS_ULI_HANDLELAZYDINTRINISCS_H
