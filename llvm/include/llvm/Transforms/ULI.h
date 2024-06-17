//===- ULI.h - ULI Transformations --------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This header file defines prototypes for accessor functions that expose passes
// in the ULI transformations library.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMATION_ULI_H
#define LLVM_TRANSFORMATION_ULI_H

namespace llvm {
// class Pass;
class ModulePass;

ModulePass *createParallelRegionReachablePass();

} // End llvm namespace

#endif