//===- ForkDTypes.h - Enum for ForkD Lowering ------------------------------*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file holds common type for ForkD
//
//===----------------------------------------------------------------------===//

#ifndef FORKD_TYPES_H_
#define FORKD_TYPES_H_

#define WORKCTX_SIZE 64

namespace llvm {

  enum class ForkDCtxType {
    I_RBP,   // Base pointer
    I_RIP,   // Instruction pointer
    I_RSP,   // Stack pointer
    // Callee register
    I_RBX,
    I_R12,
    I_R13,
    I_R14,
    I_R15,
    // Register
    I_RDI,
    I_RSI,
    I_R8,
    I_R9,
    I_R10,
    I_R11,
    I_RDX,
    I_RCX,
    I_RAX,
    // MISC
    I_JOINCNT,  // Join counter
    I_NEWRSP,   // New rsp of the parallel task
    I_OWNER,    // Who owns the job
    I_LOC,      // Location on the parallel task queue of the owner
    I_ADDRLOC,  // The address in the stack that store the location of work
    I_DEQ_CMPLT,
    I_SLOWPATH_DEQUE,
    I_EXECUTEDBY_OWNER
  };

  enum class ForkDTargetType {
    None,
    LazyD, 
    ULID,
    SIGUSRD,  
    EagerD 
  };

} // end namespace llvm

#endif
