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

#ifndef LLVM_TRANSFORMS_ULI_HANDLEULI_H
#define LLVM_TRANSFORMS_ULI_HANDLEULI_H

#include "llvm/IR/Dominators.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Pass.h"

namespace llvm {

/// The ULI intrinsic to external call pass. (new pass manager)
struct HandleUliPass
    : public PassInfoMixin<HandleUliPass> {


public:
  /// \return Preserved analyses of function \p F after transformation.
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  /// \return If we rewrite any intrinsic in function \p F.
  bool runImpl(Function &F);


};

/// \return An instance of created pass for legacy pass manager.
Pass *createHandleUliPass();

} // end namespace llvm

#endif // LLVM_TRANSFORMS_ULI_ULIINTRINSICTOEXTERNCALL_H
