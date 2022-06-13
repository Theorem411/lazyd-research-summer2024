//===- InsertLazyDEnDisUIPass.h - Emulate ULI intrinsics ---------------------===//
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

#ifndef LLVM_TRANSFORMS_ULI_INSERTLAZYD_ENDISUI_H
#define LLVM_TRANSFORMS_ULI_INSERTLAZYD_ENDISUI_H

#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Pass.h"

namespace llvm {

/// The ULI polling insertion pass.
struct InsertLazyDEnDisUIPass : public PassInfoMixin<InsertLazyDEnDisUIPass> {

public:
  /// \return Preserved analyses of function \p F after transformation.
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  /// \return If we insert any polling in function \p F.
  bool runImpl(Function &F);

private:
  /// Hold the arguments of polling function.
  SmallVector<Value *, 2> PollingArgs;
};

/// \return An instance of created pass for legacy pass manager.
Pass *createInsertLazyDEnDisUIPass();

} // end namespace llvm

#endif // LLVM_TRANSFORMS_ULI_INSERTLAZYD_ENDISUI_H
