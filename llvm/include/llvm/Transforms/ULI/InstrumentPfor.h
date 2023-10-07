//===- InstrumentPfor.cpp - Instrument pfor header  -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass attempts to store the next iteration in a local memory
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_ULI_INSTRUMENTPFOR_H
#define LLVM_TRANSFORMS_ULI_INSTRUMENTPFOR_H


#include "llvm/Pass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
//#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
//#include "llvm/IR/TypeBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <stack>


namespace llvm {
  struct InstrumentPforPass : public PassInfoMixin<InstrumentPforPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
  void instrumentLoop(Function &F, ScalarEvolution& SE, Loop* L);
  bool runInitialization(Module &M);
  bool runImpl(Function &F, ScalarEvolution& SE, LoopInfo& LI);

private:
  StructType* RequestChannelTy = nullptr;
  StructType* ResponseChannelTy = nullptr;
  bool initialized;
  enum RequestChannelFields
  {
    sendThreadId = 0,
    padding_char,
    potentialParallelTask,
    inLoop,
    padding
  };
};

Pass *createInstrumentPforPass();
}

#endif
