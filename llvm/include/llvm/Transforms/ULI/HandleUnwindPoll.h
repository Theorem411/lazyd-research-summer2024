//===- HandleUnwindPoll.h - Compile unwind poll ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass inline polling builtin
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_ULI_HANDLEUNWINDPOLL_H
#define LLVM_TRANSFORMS_ULI_HANDLEUNWINDPOLL_H

#include "llvm/IR/Dominators.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Pass.h"

namespace llvm {

struct HandleUnwindPollPass
    : public PassInfoMixin<HandleUnwindPollPass> {

  llvm::Type *BoolTy;
  bool initialized;

  bool handleUnwindPoll(BasicBlock &BB, BasicBlock* unwindPathEntry);
  BasicBlock* findUnwindPathEntry(Function &F);
  bool   detachExists(Function &F);

  StructType* RequestChannelTy = nullptr;
  StructType* ResponseChannelTy = nullptr;

  enum RequestChannelFields
  {
    sendThreadId = 0,
    padding_char,
    potentialParallelTask,
    inLoop,
    padding
  };

  Function* Get__unwindrts_unwind_ulifsim2(Module& M);

public:
  /// \return Preserved analyses of function \p F after transformation.
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  bool runInitialization(Module &M);
  bool runImpl(Function &F);

  // Is this still needed?
  struct _request_channel {};
  struct _response_channel {};
};

/// \return An instance of created pass for legacy pass manager.
Pass *createHandleUnwindPollPass();

} // end namespace llvm

#endif // LLVM_TRANSFORMS_ULI_HANDLEUNWINDPOLL_H
