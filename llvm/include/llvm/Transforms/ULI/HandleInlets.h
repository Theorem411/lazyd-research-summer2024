//===- HandleInlets.h - Compile inlets ----------------===//
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

#ifndef LLVM_TRANSFORMS_ULI_HANDLEINLETS_H
#define LLVM_TRANSFORMS_ULI_HANDLEINLETS_H

#include "llvm/IR/Dominators.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Pass.h"

namespace llvm {

struct HandleInletsPass
    : public PassInfoMixin<HandleInletsPass> {


  llvm::Type *BoolTy;

  bool handlePotentialJump(BasicBlock &BB);
public:
  /// \return Preserved analyses of function \p F after transformation.
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  bool runInitialization(Module &M);
  bool runImpl(Function &F);


};

/// \return An instance of created pass for legacy pass manager.
Pass *createHandleInletsPass();

} // end namespace llvm

#endif // LLVM_TRANSFORMS_ULI_HANDLEINLETS_H
