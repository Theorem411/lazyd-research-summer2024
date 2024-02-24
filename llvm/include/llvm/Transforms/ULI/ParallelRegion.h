//===- ParallelRegion.h -  ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass performs callgraph analysis to determine outlining strategy for 
// parallel regions as outlined functions.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_PARALLEL_REGION_H
#define LLVM_TRANSFORMS_PARALLEL_REGION_H

#include "llvm/IR/PassManager.h"

namespace llvm {
    struct ParallelRegionReachablePass : public PassInfoMixin<ParallelRegionReachablePass> {
        PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
    };

    // /// \return An instance of created pass for legacy pass manager.
    // Pass *createParallelRegionReachablePass();
}

#endif // LLVM_TRANFORMS_PARALLEL_REGION_PASS_H