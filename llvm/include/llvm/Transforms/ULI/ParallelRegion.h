//=== ParallelRegion.h 

#ifndef PARALLEL_REGION_PASS_H
#define PARALLEL_REGION_PASS_H
#include "llvm/IR/PassManager.h"

// using namespace llvm;

namespace llvm {
    struct ParallelRegionPass : public PassInfoMixin<ParallelRegionPass> {
        PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
    };
}

#endif // PARALLEL_REGION_PASS_H