//===- ULI.cpp ----------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements common infrastructure for LLVMULI.a, which
// implements the ParallelRegion analysis 
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/Passes.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
// #include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include "llvm/Transforms/ULI.h"

using namespace llvm;

/// initializeULI - Initialize all passes linked into the ULI library
void llvm::initializeULI(PassRegistry &Registry) {
    initializeParallelRegionWrapperPassPass(Registry);
}
