//===- HandleLazyDInstrumentation.h - Lower LazyD Instrumentation ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass lower LazyD Instrumentation
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_ULI_HANDLELAZYDINSTRUMENTATION_H
#define LLVM_TRANSFORMS_ULI_HANDLELAZYDINSTRUMENTATION_H

#include "llvm/IR/Dominators.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Pass.h"

namespace llvm {

struct HandleLazyDInstrumentationPass
    : public PassInfoMixin<HandleLazyDInstrumentationPass> {
  bool handleLazyDInstrumentation(Function &F);

public:
  /// \return Preserved analyses of function \p F after transformation.
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  bool runInitialization(Module &M);
  bool runImpl(Function &F);
};

/// \return An instance of created pass for legacy pass manager.
Pass *createHandleLazyDInstrumentationPass();

} // end namespace llvm

#endif // LLVM_TRANSFORMS_ULI_HANDLELAZYDINSTRUMENTATION_H
