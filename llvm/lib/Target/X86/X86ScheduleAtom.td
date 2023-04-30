//===- X86ScheduleAtom.td - X86 Atom Scheduling Definitions -*- tablegen -*-==//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the schedule class data for the Intel Atom
// in order (Saltwell-32nm/Bonnell-45nm) processors.
//
//===----------------------------------------------------------------------===//

//
// Scheduling information derived from the "Intel 64 and IA32 Architectures
// Optimization Reference Manual", Chapter 13, Section 4.
/*
// Functional Units
//    Port 0
def Port0 : FuncUnit; // ALU: ALU0, shift/rotate, load/store
                      // SIMD/FP: SIMD ALU, Shuffle,SIMD/FP multiply, divide
def Port1 : FuncUnit; // ALU: ALU1, bit processing, jump, and LEA
                      // SIMD/FP: SIMD ALU, FP Adder

def AtomItineraries : ProcessorItineraries<
  [ Port0, Port1 ],
  [], [
  // P0 only
  // InstrItinData<class, [InstrStage<N, [P0]>] >,
  // P0 or P1
  // InstrItinData<class, [InstrStage<N, [P0, P1]>] >,
  // P0 and P1
  // InstrItinData<class, [InstrStage<N, [P0], 0>,  InstrStage<N, [P1]>] >,
  //
  // Default is 1 cycle, port0 or port1
  InstrItinData<IIC_ALU_MEM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_ALU_NONMEM, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_LEA, [InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_LEA_16, [InstrStage<2, [Port0, Port1]>] >,
  // mul
  InstrItinData<IIC_MUL8, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_MUL16_MEM, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_MUL16_REG, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_MUL32_MEM, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_MUL32_REG, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_MUL64, [InstrStage<12, [Port0, Port1]>] >,
  // imul by al, ax, eax, rax
  InstrItinData<IIC_IMUL8, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL16_MEM, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL16_REG, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL32_MEM, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL32_REG, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL64, [InstrStage<12, [Port0, Port1]>] >,
  // imul reg by reg|mem
  InstrItinData<IIC_IMUL16_RM, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL16_RR, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL32_RM, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_IMUL32_RR, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_IMUL64_RM, [InstrStage<12, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL64_RR, [InstrStage<12, [Port0, Port1]>] >,
  // imul reg = reg/mem * imm
  InstrItinData<IIC_IMUL16_RRI, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL32_RRI, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_IMUL64_RRI, [InstrStage<14, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL16_RMI, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_IMUL32_RMI, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_IMUL64_RMI, [InstrStage<14, [Port0, Port1]>] >,
  // idiv
  InstrItinData<IIC_IDIV8, [InstrStage<62, [Port0, Port1]>] >,
  InstrItinData<IIC_IDIV16, [InstrStage<62, [Port0, Port1]>] >,
  InstrItinData<IIC_IDIV32, [InstrStage<62, [Port0, Port1]>] >,
  InstrItinData<IIC_IDIV64, [InstrStage<130, [Port0, Port1]>] >,
  // div
  InstrItinData<IIC_DIV8_REG, [InstrStage<50, [Port0, Port1]>] >,
  InstrItinData<IIC_DIV8_MEM, [InstrStage<68, [Port0, Port1]>] >,
  InstrItinData<IIC_DIV16, [InstrStage<50, [Port0, Port1]>] >,
  InstrItinData<IIC_DIV32, [InstrStage<50, [Port0, Port1]>] >,
  InstrItinData<IIC_DIV64, [InstrStage<130, [Port0, Port1]>] >,
  // neg/not/inc/dec
  InstrItinData<IIC_UNARY_REG, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_UNARY_MEM, [InstrStage<1, [Port0]>] >,
  // add/sub/and/or/xor/cmp/test
  InstrItinData<IIC_BIN_NONMEM, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_BIN_MEM, [InstrStage<1, [Port0]>] >,
  // adc/sbc
  InstrItinData<IIC_BIN_CARRY_NONMEM, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_BIN_CARRY_MEM, [InstrStage<1, [Port0]>] >,
  // shift/rotate
  InstrItinData<IIC_SR, [InstrStage<1, [Port0]>] >,
  // shift double
  InstrItinData<IIC_SHD16_REG_IM, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD16_REG_CL, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD16_MEM_IM, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD16_MEM_CL, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD32_REG_IM, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD32_REG_CL, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD32_MEM_IM, [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD32_MEM_CL, [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD64_REG_IM, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD64_REG_CL, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD64_MEM_IM, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_SHD64_MEM_CL, [InstrStage<9, [Port0, Port1]>] >,
  // cmov
  InstrItinData<IIC_CMOV16_RM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_CMOV16_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_CMOV32_RM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_CMOV32_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_CMOV64_RM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_CMOV64_RR, [InstrStage<1, [Port0, Port1]>] >,
  // set
  InstrItinData<IIC_SET_M, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_SET_R, [InstrStage<1, [Port0, Port1]>] >,
  // jcc
  InstrItinData<IIC_Jcc, [InstrStage<1, [Port1]>] >,
  // jcxz/jecxz/jrcxz
  InstrItinData<IIC_JCXZ, [InstrStage<4, [Port0, Port1]>] >,
  // jmp rel
  InstrItinData<IIC_JMP_REL, [InstrStage<1, [Port1]>] >,
  // jmp indirect
  InstrItinData<IIC_JMP_REG, [InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_JMP_MEM, [InstrStage<2, [Port0, Port1]>] >,
  // jmp far
  InstrItinData<IIC_JMP_FAR_MEM, [InstrStage<32, [Port0, Port1]>] >,
  InstrItinData<IIC_JMP_FAR_PTR, [InstrStage<31, [Port0, Port1]>] >,
  // loop/loope/loopne
  InstrItinData<IIC_LOOP, [InstrStage<18, [Port0, Port1]>] >,
  InstrItinData<IIC_LOOPE, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_LOOPNE, [InstrStage<17, [Port0, Port1]>] >,
  // call - all but reg/imm
  InstrItinData<IIC_CALL_RI, [InstrStage<1, [Port0], 0>,
                              InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_CALL_MEM, [InstrStage<15, [Port0, Port1]>] >,
  InstrItinData<IIC_CALL_FAR_MEM, [InstrStage<40, [Port0, Port1]>] >,
  InstrItinData<IIC_CALL_FAR_PTR, [InstrStage<39, [Port0, Port1]>] >,
  //ret
  InstrItinData<IIC_RET, [InstrStage<79, [Port0, Port1]>] >,
  InstrItinData<IIC_RET_IMM, [InstrStage<1, [Port0], 0>,  InstrStage<1, [Port1]>] >,
  //sign extension movs
  InstrItinData<IIC_MOVSX,[InstrStage<1, [Port0] >] >,
  InstrItinData<IIC_MOVSX_R16_R8, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_MOVSX_R16_M8, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_MOVSX_R16_R16, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_MOVSX_R32_R32, [InstrStage<1, [Port0, Port1]>] >,
  //zero extension movs
  InstrItinData<IIC_MOVZX,[InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MOVZX_R16_R8, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_MOVZX_R16_M8, [InstrStage<3, [Port0, Port1]>] >,

  InstrItinData<IIC_REP_MOVS, [InstrStage<75, [Port0, Port1]>] >,
  InstrItinData<IIC_REP_STOS, [InstrStage<74, [Port0, Port1]>] >,

  // SSE binary operations
  // arithmetic fp scalar
  InstrItinData<IIC_SSE_ALU_F32S_RR, [InstrStage<5, [Port1]>] >,
  InstrItinData<IIC_SSE_ALU_F32S_RM, [InstrStage<5, [Port0], 0>,
                                   InstrStage<5, [Port1]>] >,
  InstrItinData<IIC_SSE_ALU_F64S_RR, [InstrStage<5, [Port1]>] >,
  InstrItinData<IIC_SSE_ALU_F64S_RM, [InstrStage<5, [Port0], 0>,
                                   InstrStage<5, [Port1]>] >,
  InstrItinData<IIC_SSE_MUL_F32S_RR, [InstrStage<4, [Port0]>] >,
  InstrItinData<IIC_SSE_MUL_F32S_RM, [InstrStage<4, [Port0]>] >,
  InstrItinData<IIC_SSE_MUL_F64S_RR, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_SSE_MUL_F64S_RM, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_SSE_DIV_F32S_RR, [InstrStage<34, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_DIV_F32S_RM, [InstrStage<34, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_DIV_F64S_RR, [InstrStage<62, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_DIV_F64S_RM, [InstrStage<62, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_COMIS_RR, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_COMIS_RM, [InstrStage<10, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_HADDSUB_RR, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_HADDSUB_RM, [InstrStage<9, [Port0, Port1]>] >,

  // arithmetic fp parallel
  InstrItinData<IIC_SSE_ALU_F32P_RR, [InstrStage<5, [Port1]>] >,
  InstrItinData<IIC_SSE_ALU_F32P_RM, [InstrStage<5, [Port0], 0>,
                                   InstrStage<5, [Port1]>] >,
  InstrItinData<IIC_SSE_ALU_F64P_RR, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_ALU_F64P_RM, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_MUL_F32P_RR, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_SSE_MUL_F32P_RM, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_SSE_MUL_F64P_RR, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_MUL_F64P_RM, [InstrStage<10, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_DIV_F32P_RR, [InstrStage<70, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_DIV_F32P_RM, [InstrStage<70, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_DIV_F64P_RR, [InstrStage<125, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_DIV_F64P_RM, [InstrStage<125, [Port0, Port1]>] >,

  // bitwise parallel
  InstrItinData<IIC_SSE_BIT_P_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_BIT_P_RM, [InstrStage<1, [Port0]>] >,

  // arithmetic int parallel
  InstrItinData<IIC_SSE_INTALU_P_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_INTALU_P_RM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_INTALUQ_P_RR, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_INTALUQ_P_RM, [InstrStage<3, [Port0, Port1]>] >,

  // multiply int parallel
  InstrItinData<IIC_SSE_INTMUL_P_RR, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_SSE_INTMUL_P_RM, [InstrStage<5, [Port0]>] >,

  // shift parallel
  InstrItinData<IIC_SSE_INTSH_P_RR, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_INTSH_P_RM, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_INTSH_P_RI, [InstrStage<1, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_INTSHDQ_P_RI, [InstrStage<1, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_SHUFP, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_PSHUF_RI, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_PSHUF_MI, [InstrStage<1, [Port0]>] >,

  InstrItinData<IIC_SSE_PACK, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_UNPCK, [InstrStage<1, [Port0]>] >,

  InstrItinData<IIC_SSE_SQRTPS_RR, [InstrStage<70, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_SQRTPS_RM, [InstrStage<70, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_SQRTSS_RR, [InstrStage<34, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_SQRTSS_RM, [InstrStage<34, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_SQRTPD_RR, [InstrStage<125, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_SQRTPD_RM, [InstrStage<125, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_SQRTSD_RR, [InstrStage<62, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_SQRTSD_RM, [InstrStage<62, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_RSQRTPS_RR, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_RSQRTPS_RM, [InstrStage<10, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_RSQRTSS_RR, [InstrStage<4, [Port0]>] >,
  InstrItinData<IIC_SSE_RSQRTSS_RM, [InstrStage<4, [Port0]>] >,

  InstrItinData<IIC_SSE_RCPP_RR, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_RCPP_RM, [InstrStage<10, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_RCPS_RR, [InstrStage<4, [Port0]>] >,
  InstrItinData<IIC_SSE_RCPS_RM, [InstrStage<4, [Port0]>] >,

  InstrItinData<IIC_SSE_MOVMSK, [InstrStage<3, [Port0]>] >,
  InstrItinData<IIC_SSE_MASKMOV, [InstrStage<2, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_PEXTRW, [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PINSRW, [InstrStage<1, [Port0]>] >,

  InstrItinData<IIC_SSE_PABS_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PABS_RM, [InstrStage<1, [Port0]>] >,

  InstrItinData<IIC_SSE_MOV_S_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_MOV_S_RM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_MOV_S_MR, [InstrStage<1, [Port0]>] >,

  InstrItinData<IIC_SSE_MOVA_P_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_MOVA_P_RM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_MOVA_P_MR, [InstrStage<1, [Port0]>] >,

  InstrItinData<IIC_SSE_MOVU_P_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_MOVU_P_RM, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_MOVU_P_MR, [InstrStage<2, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_MOV_LH, [InstrStage<1, [Port0]>] >,

  InstrItinData<IIC_SSE_LDDQU, [InstrStage<3, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_MOVDQ, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_MOVD_ToGP, [InstrStage<3, [Port0]>] >,
  InstrItinData<IIC_SSE_MOVQ_RR, [InstrStage<1, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_MOVNT, [InstrStage<1, [Port0]>] >,

  InstrItinData<IIC_SSE_PREFETCH, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_PAUSE, [InstrStage<17, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_LFENCE, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_MFENCE, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_SFENCE, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_LDMXCSR, [InstrStage<5, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_STMXCSR, [InstrStage<15, [Port0, Port1]>] >,

  InstrItinData<IIC_SSE_PHADDSUBD_RR, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PHADDSUBD_RM, [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PHADDSUBSW_RR, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PHADDSUBSW_RM, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PHADDSUBW_RR, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PHADDSUBW_RM, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PSHUFB_RR, [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PSHUFB_RM, [InstrStage<5, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PSIGN_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_PSIGN_RM, [InstrStage<1, [Port0]>] >,

  InstrItinData<IIC_SSE_PMADD, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_SSE_PMULHRSW, [InstrStage<5, [Port0]>] >,
  InstrItinData<IIC_SSE_PALIGNRR, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_PALIGNRM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_SSE_MWAIT, [InstrStage<46, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_MONITOR, [InstrStage<45, [Port0, Port1]>] >,

  // conversions
  // to/from PD ...
  InstrItinData<IIC_SSE_CVT_PD_RR, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_PD_RM, [InstrStage<8, [Port0, Port1]>] >,
  // to/from PS except to/from PD and PS2PI
  InstrItinData<IIC_SSE_CVT_PS_RR, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_PS_RM, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_Scalar_RR, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_Scalar_RM, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_SS2SI32_RR, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_SS2SI32_RM, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_SS2SI64_RR, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_SS2SI64_RM, [InstrStage<10, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_SD2SI_RR, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_SSE_CVT_SD2SI_RM, [InstrStage<9, [Port0, Port1]>] >,

  // MMX MOVs
  InstrItinData<IIC_MMX_MOV_MM_RM,  [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_MOV_REG_MM, [InstrStage<3, [Port0]>] >,
  InstrItinData<IIC_MMX_MOVQ_RM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_MOVQ_RR, [InstrStage<1, [Port0, Port1]>] >,
  // other MMX
  InstrItinData<IIC_MMX_ALU_RM,  [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_ALU_RR,  [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_ALUQ_RM, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_ALUQ_RR, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_PHADDSUBW_RM, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_PHADDSUBW_RR, [InstrStage<5, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_PHADDSUBD_RM, [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_PHADDSUBD_RR, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_PMUL, [InstrStage<4, [Port0]>] >,
  InstrItinData<IIC_MMX_MISC_FUNC_MEM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_MISC_FUNC_REG, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_PSADBW,   [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_SHIFT_RI, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_SHIFT_RM, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_SHIFT_RR, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_UNPCK_H_RM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_UNPCK_H_RR, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_UNPCK_L, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_PCK_RM,  [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_PCK_RR,  [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_PSHUF,   [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_PEXTR,   [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_PINSRW,  [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_MASKMOV, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MMX_MOVMSK, [InstrStage<3, [Port0]>] >,
  // conversions
  // from/to PD
  InstrItinData<IIC_MMX_CVT_PD_RR, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_CVT_PD_RM, [InstrStage<8, [Port0, Port1]>] >,
  // from/to PI
  InstrItinData<IIC_MMX_CVT_PS_RR, [InstrStage<5, [Port1]>] >,
  InstrItinData<IIC_MMX_CVT_PS_RM, [InstrStage<5, [Port0], 0>,
                                    InstrStage<5, [Port1]>]>,

  InstrItinData<IIC_CMPX_LOCK, [InstrStage<14, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPX_LOCK_8, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPX_LOCK_8B, [InstrStage<18, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPX_LOCK_16B, [InstrStage<22, [Port0, Port1]>] >,

  InstrItinData<IIC_XADD_LOCK_MEM, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_XADD_LOCK_MEM, [InstrStage<3, [Port0, Port1]>] >,

  InstrItinData<IIC_FILD, [InstrStage<5, [Port0], 0>, InstrStage<5, [Port1]>] >,
  InstrItinData<IIC_FLD,  [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_FLD80, [InstrStage<4, [Port0, Port1]>] >,

  InstrItinData<IIC_FST,   [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_FST80, [InstrStage<5, [Port0, Port1]>] >,
  InstrItinData<IIC_FIST,  [InstrStage<6, [Port0, Port1]>] >,

  InstrItinData<IIC_FCMOV,  [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_FLDZ,   [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_FUCOM,  [InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_FUCOMI, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_FCOMI,  [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_FNSTSW, [InstrStage<10, [Port0, Port1]>] >,
  InstrItinData<IIC_FNSTCW, [InstrStage<8, [Port0, Port1]>] >,
  InstrItinData<IIC_FLDCW,  [InstrStage<5, [Port0, Port1]>] >,
  InstrItinData<IIC_FNINIT, [InstrStage<63, [Port0, Port1]>] >,
  InstrItinData<IIC_FFREE,  [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_FNCLEX, [InstrStage<25, [Port0, Port1]>] >,
  InstrItinData<IIC_WAIT,  [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_FXAM,  [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_FNOP,  [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_FLDL,  [InstrStage<10, [Port0, Port1]>] >,
  InstrItinData<IIC_F2XM1,  [InstrStage<99, [Port0, Port1]>] >,
  InstrItinData<IIC_FYL2X,  [InstrStage<146, [Port0, Port1]>] >,
  InstrItinData<IIC_FPTAN,  [InstrStage<168, [Port0, Port1]>] >,
  InstrItinData<IIC_FPATAN,  [InstrStage<183, [Port0, Port1]>] >,
  InstrItinData<IIC_FXTRACT,  [InstrStage<25, [Port0, Port1]>] >,
  InstrItinData<IIC_FPREM1,  [InstrStage<71, [Port0, Port1]>] >,
  InstrItinData<IIC_FPSTP,  [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_FPREM,  [InstrStage<55, [Port0, Port1]>] >,
  InstrItinData<IIC_FYL2XP1,  [InstrStage<147, [Port0, Port1]>] >,
  InstrItinData<IIC_FSINCOS,  [InstrStage<174, [Port0, Port1]>] >,
  InstrItinData<IIC_FRNDINT,  [InstrStage<46, [Port0, Port1]>] >,
  InstrItinData<IIC_FSCALE,  [InstrStage<77, [Port0, Port1]>] >,
  InstrItinData<IIC_FCOMPP,  [InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_FXSAVE,  [InstrStage<140, [Port0, Port1]>] >,
  InstrItinData<IIC_FXRSTOR,  [InstrStage<141, [Port0, Port1]>] >,
  InstrItinData<IIC_FXCH, [InstrStage<1, [Port0], 0>, InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_FSIGN,  [InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_FSQRT,  [InstrStage<71, [Port0, Port1]>] >,

  // System instructions
  InstrItinData<IIC_CPUID, [InstrStage<121, [Port0, Port1]>] >,
  InstrItinData<IIC_INT,   [InstrStage<127, [Port0, Port1]>] >,
  InstrItinData<IIC_INT3,  [InstrStage<130, [Port0, Port1]>] >,
  InstrItinData<IIC_INVD,  [InstrStage<1003, [Port0, Port1]>] >,
  InstrItinData<IIC_INVLPG, [InstrStage<71, [Port0, Port1]>] >,
  InstrItinData<IIC_IRET,  [InstrStage<109, [Port0, Port1]>] >,
  InstrItinData<IIC_UIRET,  [InstrStage<109, [Port0, Port1]>] >,
  InstrItinData<IIC_ULIRET,  [InstrStage<109, [Port0, Port1]>] >,
  InstrItinData<IIC_HLT,   [InstrStage<121, [Port0, Port1]>] >,
  InstrItinData<IIC_LXS,   [InstrStage<10, [Port0, Port1]>] >,
  InstrItinData<IIC_LTR,   [InstrStage<83, [Port0, Port1]>] >,
  InstrItinData<IIC_RDTSC, [InstrStage<30, [Port0, Port1]>] >,
  InstrItinData<IIC_RDTSCP, [InstrStage<30, [Port0, Port1]>] >,
  InstrItinData<IIC_RSM,   [InstrStage<741, [Port0, Port1]>] >,
  InstrItinData<IIC_SIDT,  [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_SGDT,  [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_SLDT,  [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_STR,    [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_SWAPGS, [InstrStage<22, [Port0, Port1]>] >,
  InstrItinData<IIC_SYSCALL, [InstrStage<96, [Port0, Port1]>] >,
  InstrItinData<IIC_SYS_ENTER_EXIT, [InstrStage<88, [Port0, Port1]>] >,

  InstrItinData<IIC_IN_RR,  [InstrStage<94, [Port0, Port1]>] >,
  InstrItinData<IIC_IN_RI,  [InstrStage<92, [Port0, Port1]>] >,
  InstrItinData<IIC_OUT_RR, [InstrStage<68, [Port0, Port1]>] >,
  InstrItinData<IIC_OUT_IR, [InstrStage<72, [Port0, Port1]>] >,
  InstrItinData<IIC_INS,    [InstrStage<59, [Port0, Port1]>] >,

  InstrItinData<IIC_MOV_REG_DR, [InstrStage<88, [Port0, Port1]>] >,
  InstrItinData<IIC_MOV_DR_REG, [InstrStage<123, [Port0, Port1]>] >,
  // worst case for mov REG_CRx
  InstrItinData<IIC_MOV_REG_CR, [InstrStage<12, [Port0, Port1]>] >,
  InstrItinData<IIC_MOV_CR_REG, [InstrStage<136, [Port0, Port1]>] >,

  InstrItinData<IIC_MOV_REG_SR, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_MOV_MEM_SR, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_MOV_SR_REG, [InstrStage<21, [Port0, Port1]>] >,
  InstrItinData<IIC_MOV_SR_MEM, [InstrStage<26, [Port0, Port1]>] >,
  // LAR
  InstrItinData<IIC_LAR_RM,  [InstrStage<50, [Port0, Port1]>] >,
  InstrItinData<IIC_LAR_RR,  [InstrStage<54, [Port0, Port1]>] >,
  // LSL
  InstrItinData<IIC_LSL_RM,  [InstrStage<46, [Port0, Port1]>] >,
  InstrItinData<IIC_LSL_RR,  [InstrStage<49, [Port0, Port1]>] >,

  InstrItinData<IIC_LGDT, [InstrStage<44, [Port0, Port1]>] >,
  InstrItinData<IIC_LIDT, [InstrStage<44, [Port0, Port1]>] >,
  InstrItinData<IIC_LLDT_REG, [InstrStage<60, [Port0, Port1]>] >,
  InstrItinData<IIC_LLDT_MEM, [InstrStage<64, [Port0, Port1]>] >,
  // push control register, segment registers
  InstrItinData<IIC_PUSH_CS, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_PUSH_SR, [InstrStage<2, [Port0, Port1]>] >,
  // pop control register, segment registers
  InstrItinData<IIC_POP_SR,    [InstrStage<29, [Port0, Port1]>] >,
  InstrItinData<IIC_POP_SR_SS, [InstrStage<48, [Port0, Port1]>] >,
  // VERR, VERW
  InstrItinData<IIC_VERR,     [InstrStage<41, [Port0, Port1]>] >,
  InstrItinData<IIC_VERW_REG, [InstrStage<51, [Port0, Port1]>] >,
  InstrItinData<IIC_VERW_MEM, [InstrStage<50, [Port0, Port1]>] >,
  // WRMSR, RDMSR
  InstrItinData<IIC_WRMSR, [InstrStage<202, [Port0, Port1]>] >,
  InstrItinData<IIC_RDMSR, [InstrStage<78, [Port0, Port1]>] >,
  InstrItinData<IIC_RDPMC, [InstrStage<46, [Port0, Port1]>] >,
  // SMSW, LMSW
  InstrItinData<IIC_SMSW, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_LMSW_REG, [InstrStage<69, [Port0, Port1]>] >,
  InstrItinData<IIC_LMSW_MEM, [InstrStage<67, [Port0, Port1]>] >,

  InstrItinData<IIC_ENTER, [InstrStage<32, [Port0, Port1]>] >,
  InstrItinData<IIC_LEAVE, [InstrStage<2, [Port0, Port1]>] >,

  InstrItinData<IIC_POP_MEM, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_POP_REG16, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_POP_REG, [InstrStage<1, [Port0], 0>,
                            InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_POP_F, [InstrStage<32, [Port0, Port1]>] >,
  InstrItinData<IIC_POP_FD, [InstrStage<26, [Port0, Port1]>] >,
  InstrItinData<IIC_POP_A, [InstrStage<9, [Port0, Port1]>] >,

  InstrItinData<IIC_PUSH_IMM, [InstrStage<1, [Port0], 0>,
                               InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_PUSH_MEM, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_PUSH_REG, [InstrStage<1, [Port0], 0>,
                               InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_PUSH_F, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_PUSH_A, [InstrStage<8, [Port0, Port1]>] >,

  InstrItinData<IIC_BSWAP, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_BIT_SCAN_MEM, [InstrStage<16, [Port0, Port1]>] >,
  InstrItinData<IIC_BIT_SCAN_REG, [InstrStage<16, [Port0, Port1]>] >,
  InstrItinData<IIC_MOVS, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_STOS, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_SCAS, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPS, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_MOV, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_MOV_MEM, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_AHF, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_BT_MI, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_BT_MR, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_BT_RI, [InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_BT_RR, [InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_BTX_MI, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_BTX_MR, [InstrStage<11, [Port0, Port1]>] >,
  InstrItinData<IIC_BTX_RI, [InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_BTX_RR, [InstrStage<1, [Port1]>] >,
  InstrItinData<IIC_XCHG_REG, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_XCHG_MEM, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_XADD_REG, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_XADD_MEM, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPXCHG_MEM, [InstrStage<14, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPXCHG_REG, [InstrStage<15, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPXCHG_MEM8, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPXCHG_REG8, [InstrStage<9, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPXCHG_8B, [InstrStage<18, [Port0, Port1]>] >,
  InstrItinData<IIC_CMPXCHG_16B, [InstrStage<22, [Port0, Port1]>] >,
  InstrItinData<IIC_LODS, [InstrStage<2, [Port0, Port1]>] >,
  InstrItinData<IIC_OUTS, [InstrStage<74, [Port0, Port1]>] >,
  InstrItinData<IIC_CLC, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_CLD, [InstrStage<3, [Port0, Port1]>] >,
  InstrItinData<IIC_CLI, [InstrStage<14, [Port0, Port1]>] >,
  InstrItinData<IIC_CMC, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_CLTS, [InstrStage<33, [Port0, Port1]>] >,
  InstrItinData<IIC_STC, [InstrStage<1, [Port0, Port1]>] >,
  InstrItinData<IIC_STI, [InstrStage<17, [Port0, Port1]>] >,
  InstrItinData<IIC_STD, [InstrStage<21, [Port0, Port1]>] >,
  InstrItinData<IIC_XLAT, [InstrStage<6, [Port0, Port1]>] >,
  InstrItinData<IIC_AAA, [InstrStage<13, [Port0, Port1]>] >,
  InstrItinData<IIC_AAD, [InstrStage<7, [Port0, Port1]>] >,
  InstrItinData<IIC_AAM, [InstrStage<21, [Port0, Port1]>] >,
  InstrItinData<IIC_AAS, [InstrStage<13, [Port0, Port1]>] >,
  InstrItinData<IIC_DAA, [InstrStage<18, [Port0, Port1]>] >,
  InstrItinData<IIC_DAS, [InstrStage<20, [Port0, Port1]>] >,
  InstrItinData<IIC_BOUND, [InstrStage<11, [Port0, Port1]>] >,
  InstrItinData<IIC_ARPL_REG, [InstrStage<24, [Port0, Port1]>] >,
  InstrItinData<IIC_ARPL_MEM, [InstrStage<23, [Port0, Port1]>] >,
  InstrItinData<IIC_MOVBE, [InstrStage<1, [Port0]>] >,
  InstrItinData<IIC_CBW, [InstrStage<4, [Port0, Port1]>] >,
  InstrItinData<IIC_MMX_EMMS, [InstrStage<5, [Port0, Port1]>] >,

  InstrItinData<IIC_NOP, [InstrStage<1, [Port0, Port1]>] >
  ]>;
*/

// Atom machine model.
def AtomModel : SchedMachineModel {
  let IssueWidth = 2;  // Allows 2 instructions per scheduling group.
  let MicroOpBufferSize = 0; // In-order execution, always hide latency.
  let LoadLatency = 3; // Expected cycles, may be overriden.
  let HighLatency = 30;// Expected, may be overriden.

  // On the Atom, the throughput for taken branches is 2 cycles. For small
  // simple loops, expand by a small factor to hide the backedge cost.
  let LoopMicroOpBufferSize = 10;
  let PostRAScheduler = 1;
  let CompleteModel = 0;
}

let SchedModel = AtomModel in {

// Functional Units
def AtomPort0 : ProcResource<1>; // ALU: ALU0, shift/rotate, load/store
                                 // SIMD/FP: SIMD ALU, Shuffle,SIMD/FP multiply, divide
def AtomPort1 : ProcResource<1>; // ALU: ALU1, bit processing, jump, and LEA
                                 // SIMD/FP: SIMD ALU, FP Adder

// NOTE: This is for ops that can use EITHER port, not for ops that require BOTH ports.
def AtomPort01 : ProcResGroup<[AtomPort0, AtomPort1]>;

// Loads are 3 cycles, so ReadAfterLd registers needn't be available until 3
// cycles after the memory operand.
def : ReadAdvance<ReadAfterLd, 3>;
def : ReadAdvance<ReadAfterVecLd, 3>;
def : ReadAdvance<ReadAfterVecXLd, 3>;
def : ReadAdvance<ReadAfterVecYLd, 3>;

def : ReadAdvance<ReadInt2Fpu, 0>;

// This multiclass defines the resource usage for variants with and without
// folded loads.
multiclass AtomWriteResPair<X86FoldableSchedWrite SchedRW,
                            list<ProcResourceKind> RRPorts,
                            list<ProcResourceKind> RMPorts,
                            int RRLat = 1, int RMLat = 1,
                            list<int> RRRes = [1],
                            list<int> RMRes = [1],
                            int RRUOps = 1,
                            int RMUOps = 1> {
  // Register variant.
  def : WriteRes<SchedRW, RRPorts> {
    let Latency = RRLat;
    let ResourceCycles = RRRes;
    let NumMicroOps = RRUOps;
  }

  // Memory variant.
  def : WriteRes<SchedRW.Folded, RMPorts> {
    let Latency = RMLat;
    let ResourceCycles = RMRes;
    let NumMicroOps = RMUOps;
  }
}

// A folded store needs a cycle on Port0 for the store data.
def : WriteRes<WriteRMW, [AtomPort0]>;

////////////////////////////////////////////////////////////////////////////////
// Arithmetic.
////////////////////////////////////////////////////////////////////////////////

defm : AtomWriteResPair<WriteALU,    [AtomPort01], [AtomPort0]>;
defm : AtomWriteResPair<WriteADC,    [AtomPort01], [AtomPort0]>;

defm : AtomWriteResPair<WriteIMul8,     [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  7,  7,  [7,7],  [7,7], 3, 3>;
defm : AtomWriteResPair<WriteIMul16,    [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  7,  8,  [7,7],  [8,8], 4, 5>;
defm : AtomWriteResPair<WriteIMul16Imm, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [6,6],  [7,7], 2, 3>;
defm : AtomWriteResPair<WriteIMul16Reg, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [6,6],  [7,7], 2, 3>;
defm : AtomWriteResPair<WriteIMul32,    [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [6,6],  [7,7], 3, 4>;
defm : AtomWriteResPair<WriteIMul32Imm, [AtomPort0],  [AtomPort0],   5,  5,  [5],  [5]>;
defm : AtomWriteResPair<WriteIMul32Reg, [AtomPort0],  [AtomPort0],   5,  5,  [5],  [5]>;
defm : AtomWriteResPair<WriteIMul64,    [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 12, 12, [12,12], [12,12], 8, 8>;
defm : AtomWriteResPair<WriteIMul64Imm, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 14, 14, [14,14], [14,14], 7, 7>;
defm : AtomWriteResPair<WriteIMul64Reg, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 12, 12, [12,12], [12,12], 6, 6>;
defm : X86WriteResUnsupported<WriteIMulH>;
defm : X86WriteResUnsupported<WriteIMulHLd>;
defm : X86WriteResPairUnsupported<WriteMULX32>;
defm : X86WriteResPairUnsupported<WriteMULX64>;

defm : X86WriteRes<WriteXCHG,        [AtomPort01], 2, [2], 1>;
defm : X86WriteRes<WriteBSWAP32,     [AtomPort0], 1, [1], 1>;
defm : X86WriteRes<WriteBSWAP64,     [AtomPort0], 1, [1], 1>;
defm : AtomWriteResPair<WriteCMPXCHG, [AtomPort01], [AtomPort01], 15, 15, [15]>;
defm : X86WriteRes<WriteCMPXCHGRMW,   [AtomPort01, AtomPort0], 1, [1, 1], 1>;

defm : AtomWriteResPair<WriteDiv8,   [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 50, 68, [50,50], [68,68],  9,  9>;
defm : AtomWriteResPair<WriteDiv16,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 50, 50, [50,50], [50,50], 12, 12>;
defm : AtomWriteResPair<WriteDiv32,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 50, 50, [50,50], [50,50], 12, 12>;
defm : AtomWriteResPair<WriteDiv64,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],130,130,[130,130],[130,130], 38, 38>;
defm : AtomWriteResPair<WriteIDiv8,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 62, 62, [62,62], [62,62], 26, 26>;
defm : AtomWriteResPair<WriteIDiv16, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 62, 62, [62,62], [62,62], 29, 29>;
defm : AtomWriteResPair<WriteIDiv32, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 62, 62, [62,62], [62,62], 29, 29>;
defm : AtomWriteResPair<WriteIDiv64, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],130,130,[130,130],[130,130], 60, 60>;

defm : X86WriteResPairUnsupported<WriteCRC32>;

defm : AtomWriteResPair<WriteCMOV,  [AtomPort01], [AtomPort0]>;
defm : X86WriteRes<WriteFCMOV, [AtomPort01], 9, [9], 1>; // x87 conditional move.

def  : WriteRes<WriteSETCC, [AtomPort01]>;
def  : WriteRes<WriteSETCCStore, [AtomPort01]> {
  let Latency = 2;
  let ResourceCycles = [2];
}
def  : WriteRes<WriteLAHFSAHF, [AtomPort01]> {
  let Latency = 2;
  let ResourceCycles = [2];
}
defm : X86WriteRes<WriteBitTest,         [AtomPort1],  1, [1], 1>;
defm : X86WriteRes<WriteBitTestImmLd,    [AtomPort0],  1, [1], 1>;
defm : X86WriteRes<WriteBitTestRegLd,    [AtomPort01], 9, [9], 1>;
defm : X86WriteRes<WriteBitTestSet,      [AtomPort1],  1, [1], 1>;
//defm : X86WriteRes<WriteBitTestSetImmLd, [AtomPort1],  1, [1], 1>;
//defm : X86WriteRes<WriteBitTestSetRegLd, [AtomPort1],  1, [1], 1>;

// This is for simple LEAs with one or two input operands.
def : WriteRes<WriteLEA, [AtomPort1]>;

// Bit counts.
defm : AtomWriteResPair<WriteBSF, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 16, 16, [16,16], [16,16], 10, 10>;
defm : AtomWriteResPair<WriteBSR, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 16, 16, [16,16], [16,16], 10, 10>;
defm : X86WriteResPairUnsupported<WritePOPCNT>;
defm : X86WriteResPairUnsupported<WriteLZCNT>;
defm : X86WriteResPairUnsupported<WriteTZCNT>;

// BMI1 BEXTR/BLS, BMI2 BZHI
defm : X86WriteResPairUnsupported<WriteBEXTR>;
defm : X86WriteResPairUnsupported<WriteBLS>;
defm : X86WriteResPairUnsupported<WriteBZHI>;

////////////////////////////////////////////////////////////////////////////////
// Integer shifts and rotates.
////////////////////////////////////////////////////////////////////////////////

defm : AtomWriteResPair<WriteShift,    [AtomPort0], [AtomPort0]>;
defm : AtomWriteResPair<WriteShiftCL,  [AtomPort0], [AtomPort0]>;
defm : AtomWriteResPair<WriteRotate,   [AtomPort0], [AtomPort0]>;
defm : AtomWriteResPair<WriteRotateCL, [AtomPort0], [AtomPort0]>;

defm : X86WriteRes<WriteSHDrri, [AtomPort01], 2, [2], 1>;
defm : X86WriteRes<WriteSHDrrcl,[AtomPort01], 2, [2], 1>;
defm : X86WriteRes<WriteSHDmri, [AtomPort01], 4, [4], 1>;
defm : X86WriteRes<WriteSHDmrcl,[AtomPort01], 4, [4], 1>;

////////////////////////////////////////////////////////////////////////////////
// Loads, stores, and moves, not folded with other operations.
////////////////////////////////////////////////////////////////////////////////

def : WriteRes<WriteLoad,    [AtomPort0]>;
def : WriteRes<WriteStore,   [AtomPort0]>;
def : WriteRes<WriteStoreNT, [AtomPort0]>;
def : WriteRes<WriteMove,    [AtomPort01]>;
defm : X86WriteResUnsupported<WriteVecMaskedGatherWriteback>;

// Treat misc copies as a move.
def : InstRW<[WriteMove], (instrs COPY)>;

////////////////////////////////////////////////////////////////////////////////
// Idioms that clear a register, like xorps %xmm0, %xmm0.
// These can often bypass execution ports completely.
////////////////////////////////////////////////////////////////////////////////

def : WriteRes<WriteZero,  []>;

////////////////////////////////////////////////////////////////////////////////
// Branches don't produce values, so they have no latency, but they still
// consume resources. Indirect branches can fold loads.
////////////////////////////////////////////////////////////////////////////////

defm : AtomWriteResPair<WriteJump, [AtomPort1], [AtomPort1]>;

////////////////////////////////////////////////////////////////////////////////
// Special case scheduling classes.
////////////////////////////////////////////////////////////////////////////////

def : WriteRes<WriteSystem,     [AtomPort01]> { let Latency = 100; }
def : WriteRes<WriteMicrocoded, [AtomPort01]> { let Latency = 100; }
def : WriteRes<WriteFence,      [AtomPort0]>;

// Nops don't have dependencies, so there's no actual latency, but we set this
// to '1' to tell the scheduler that the nop uses an ALU slot for a cycle.
def : WriteRes<WriteNop, [AtomPort01]>;

////////////////////////////////////////////////////////////////////////////////
// Floating point. This covers both scalar and vector operations.
////////////////////////////////////////////////////////////////////////////////

defm : X86WriteRes<WriteFLD0,       [AtomPort01], 1, [1], 1>;
defm : X86WriteRes<WriteFLD1,       [AtomPort01], 6, [6], 1>;
def  : WriteRes<WriteFLoad,         [AtomPort0]>;
def  : WriteRes<WriteFLoadX,        [AtomPort0]>;
defm : X86WriteResUnsupported<WriteFLoadY>;
defm : X86WriteResUnsupported<WriteFMaskedLoad>;
defm : X86WriteResUnsupported<WriteFMaskedLoadY>;

def  : WriteRes<WriteFStore,        [AtomPort0]>;
def  : WriteRes<WriteFStoreX,       [AtomPort0]>;
defm : X86WriteResUnsupported<WriteFStoreY>;
def  : WriteRes<WriteFStoreNT,      [AtomPort0]>;
def  : WriteRes<WriteFStoreNTX,     [AtomPort0]>;
defm : X86WriteResUnsupported<WriteFStoreNTY>;
defm : X86WriteResUnsupported<WriteFMaskedStore32>;
defm : X86WriteResUnsupported<WriteFMaskedStore32Y>;
defm : X86WriteResUnsupported<WriteFMaskedStore64>;
defm : X86WriteResUnsupported<WriteFMaskedStore64Y>;

def  : WriteRes<WriteFMove,         [AtomPort01]>;
def  : WriteRes<WriteFMoveX,        [AtomPort01]>;
defm : X86WriteResUnsupported<WriteFMoveY>;
defm : X86WriteResUnsupported<WriteFMoveZ>;

defm : X86WriteRes<WriteEMMS,       [AtomPort01], 5, [5], 1>;

defm : AtomWriteResPair<WriteFAdd,           [AtomPort1], [AtomPort0,AtomPort1],  5,  5,  [1],  [1,1]>;
defm : AtomWriteResPair<WriteFAddX,          [AtomPort1], [AtomPort0,AtomPort1],  5,  5,  [1],  [1,1]>;
defm : X86WriteResPairUnsupported<WriteFAddY>;
defm : X86WriteResPairUnsupported<WriteFAddZ>;
defm : AtomWriteResPair<WriteFAdd64,         [AtomPort1], [AtomPort0,AtomPort1],  5,  5,  [1],  [1,1]>;
defm : AtomWriteResPair<WriteFAdd64X,        [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [5,5],  [6,6], 3, 4>;
defm : X86WriteResPairUnsupported<WriteFAdd64Y>;
defm : X86WriteResPairUnsupported<WriteFAdd64Z>;
defm : AtomWriteResPair<WriteFCmp,           [AtomPort1], [AtomPort0,AtomPort1],  5,  5,  [1],  [1,1]>;
defm : AtomWriteResPair<WriteFCmpX,          [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [5,5],  [6,6], 3, 4>;
defm : X86WriteResPairUnsupported<WriteFCmpY>;
defm : X86WriteResPairUnsupported<WriteFCmpZ>;
defm : AtomWriteResPair<WriteFCmp64,         [AtomPort1], [AtomPort0,AtomPort1],  5,  5,  [1],  [1,1]>;
defm : AtomWriteResPair<WriteFCmp64X,        [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [5,5],  [6,6], 3, 4>;
defm : X86WriteResPairUnsupported<WriteFCmp64Y>;
defm : X86WriteResPairUnsupported<WriteFCmp64Z>;
defm : AtomWriteResPair<WriteFCom,           [AtomPort0],  [AtomPort0],  5,  5,  [5],  [5]>;
defm : AtomWriteResPair<WriteFComX,          [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  9, 10,  [9,9],[10,10], 4, 5>;
defm : AtomWriteResPair<WriteFMul,           [AtomPort0],  [AtomPort0],  4,  4,  [2],  [2]>;
defm : AtomWriteResPair<WriteFMulX,          [AtomPort0],  [AtomPort0],  5,  5,  [2],  [2]>;
defm : X86WriteResPairUnsupported<WriteFMulY>;
defm : X86WriteResPairUnsupported<WriteFMulZ>;
defm : AtomWriteResPair<WriteFMul64,         [AtomPort0],  [AtomPort0],  5,  5,  [2],  [2]>;
defm : AtomWriteResPair<WriteFMul64X,        [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  9, 10,  [9,9],[10,10], 6, 7>;
defm : X86WriteResPairUnsupported<WriteFMul64Y>;
defm : X86WriteResPairUnsupported<WriteFMul64Z>;
defm : AtomWriteResPair<WriteFRcp,           [AtomPort0],  [AtomPort0],  4,  4,  [4],  [4]>;
defm : AtomWriteResPair<WriteFRcpX,          [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  9, 10,  [9,9], [10,10], 5, 6>;
defm : X86WriteResPairUnsupported<WriteFRcpY>;
defm : X86WriteResPairUnsupported<WriteFRcpZ>;
defm : AtomWriteResPair<WriteFRsqrt,         [AtomPort0],  [AtomPort0],  4,  4,  [4],  [4]>;
defm : AtomWriteResPair<WriteFRsqrtX,        [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  9, 10,  [9,9], [10,10], 5, 6>;
defm : X86WriteResPairUnsupported<WriteFRsqrtY>;
defm : X86WriteResPairUnsupported<WriteFRsqrtZ>;
defm : AtomWriteResPair<WriteFDiv,          [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 34, 34, [34,34], [34,34], 3, 4>;
defm : AtomWriteResPair<WriteFDivX,         [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 70, 70, [70,70], [70,70], 6, 7>;
defm : X86WriteResPairUnsupported<WriteFDivY>;
defm : X86WriteResPairUnsupported<WriteFDivZ>;
defm : AtomWriteResPair<WriteFDiv64,        [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 62, 62,  [62,62],  [62,62], 3, 4>;
defm : AtomWriteResPair<WriteFDiv64X,       [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],125,125,[125,125],[125,125], 6, 7>;
defm : X86WriteResPairUnsupported<WriteFDiv64Y>;
defm : X86WriteResPairUnsupported<WriteFDiv64Z>;
defm : AtomWriteResPair<WriteFSqrt,         [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 34, 34, [34,34], [34,34], 3, 4>;
defm : AtomWriteResPair<WriteFSqrtX,        [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 70, 70, [70,70], [70,70], 5, 6>;
defm : X86WriteResPairUnsupported<WriteFSqrtY>;
defm : X86WriteResPairUnsupported<WriteFSqrtZ>;
defm : AtomWriteResPair<WriteFSqrt64,       [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 62, 62,  [62,62],  [62,62], 3, 4>;
defm : AtomWriteResPair<WriteFSqrt64X,      [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],125,125,[125,125],[125,125], 5, 6>;
defm : X86WriteResPairUnsupported<WriteFSqrt64Y>;
defm : X86WriteResPairUnsupported<WriteFSqrt64Z>;
defm : AtomWriteResPair<WriteFSqrt80,        [AtomPort0],  [AtomPort0], 71, 71, [71], [71]>;
defm : AtomWriteResPair<WriteFSign,          [AtomPort1],  [AtomPort1]>;
defm : AtomWriteResPair<WriteFRnd,           [AtomPort0],  [AtomPort0],  5,  5,  [5],  [5]>;
defm : X86WriteResPairUnsupported<WriteFRndY>;
defm : X86WriteResPairUnsupported<WriteFRndZ>;
defm : AtomWriteResPair<WriteFLogic,        [AtomPort01],  [AtomPort0]>;
defm : X86WriteResPairUnsupported<WriteFLogicY>;
defm : X86WriteResPairUnsupported<WriteFLogicZ>;
defm : AtomWriteResPair<WriteFTest,         [AtomPort01],  [AtomPort0]>;
defm : X86WriteResPairUnsupported<WriteFTestY>;
defm : X86WriteResPairUnsupported<WriteFTestZ>;
defm : AtomWriteResPair<WriteFShuffle,       [AtomPort0],  [AtomPort0]>;
defm : X86WriteResPairUnsupported<WriteFShuffleY>;
defm : X86WriteResPairUnsupported<WriteFShuffleZ>;
defm : X86WriteResPairUnsupported<WriteFVarShuffle>;
defm : X86WriteResPairUnsupported<WriteFVarShuffleY>;
defm : X86WriteResPairUnsupported<WriteFVarShuffleZ>;
defm : X86WriteResPairUnsupported<WriteFMA>;
defm : X86WriteResPairUnsupported<WriteFMAX>;
defm : X86WriteResPairUnsupported<WriteFMAY>;
defm : X86WriteResPairUnsupported<WriteFMAZ>;
defm : X86WriteResPairUnsupported<WriteDPPD>;
defm : X86WriteResPairUnsupported<WriteDPPS>;
defm : X86WriteResPairUnsupported<WriteDPPSY>;
defm : X86WriteResPairUnsupported<WriteDPPSZ>;
defm : X86WriteResPairUnsupported<WriteFBlend>;
defm : X86WriteResPairUnsupported<WriteFBlendY>;
defm : X86WriteResPairUnsupported<WriteFBlendZ>;
defm : X86WriteResPairUnsupported<WriteFVarBlend>;
defm : X86WriteResPairUnsupported<WriteFVarBlendY>;
defm : X86WriteResPairUnsupported<WriteFVarBlendZ>;
defm : X86WriteResPairUnsupported<WriteFShuffle256>;
defm : X86WriteResPairUnsupported<WriteFVarShuffle256>;

////////////////////////////////////////////////////////////////////////////////
// Conversions.
////////////////////////////////////////////////////////////////////////////////

defm : AtomWriteResPair<WriteCvtSS2I,   [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  8,  9,  [8,8],  [9,9], 3, 4>;
defm : AtomWriteResPair<WriteCvtPS2I,   [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [6,6],  [7,7], 3, 4>;
defm : X86WriteResPairUnsupported<WriteCvtPS2IY>;
defm : X86WriteResPairUnsupported<WriteCvtPS2IZ>;
defm : AtomWriteResPair<WriteCvtSD2I,   [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  8,  9,  [8,8],[10,10], 3, 4>;
defm : AtomWriteResPair<WriteCvtPD2I,   [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  7,  8,  [7,7],  [8,8], 4, 5>;
defm : X86WriteResPairUnsupported<WriteCvtPD2IY>;
defm : X86WriteResPairUnsupported<WriteCvtPD2IZ>;

defm : AtomWriteResPair<WriteCvtI2SS,   [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [6,6],  [6,6], 3, 1>;
defm : AtomWriteResPair<WriteCvtI2PS,   [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [6,6],  [7,7], 3, 4>;
defm : X86WriteResPairUnsupported<WriteCvtI2PSY>;
defm : X86WriteResPairUnsupported<WriteCvtI2PSZ>;
defm : AtomWriteResPair<WriteCvtI2SD,   [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [6,6],  [7,7], 3, 3>;
defm : AtomWriteResPair<WriteCvtI2PD,   [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  7,  8,  [6,6],  [7,7], 3, 4>;
defm : X86WriteResPairUnsupported<WriteCvtI2PDY>;
defm : X86WriteResPairUnsupported<WriteCvtI2PDZ>;

defm : AtomWriteResPair<WriteCvtSS2SD,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  6,  7,  [6,6],  [7,7], 3, 4>;
defm : AtomWriteResPair<WriteCvtPS2PD,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1],  7,  8,  [6,6],  [7,7], 4, 5>;
defm : X86WriteResPairUnsupported<WriteCvtPS2PDY>;
defm : X86WriteResPairUnsupported<WriteCvtPS2PDZ>;
defm : AtomWriteResPair<WriteCvtSD2SS,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 10, 11,[10,10],[12,12], 3, 4>;
defm : AtomWriteResPair<WriteCvtPD2PS,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 11, 12,[11,11],[12,12], 4, 5>;
defm : X86WriteResPairUnsupported<WriteCvtPD2PSY>;
defm : X86WriteResPairUnsupported<WriteCvtPD2PSZ>;

defm : X86WriteResPairUnsupported<WriteCvtPH2PS>;
defm : X86WriteResPairUnsupported<WriteCvtPH2PSY>;
defm : X86WriteResPairUnsupported<WriteCvtPH2PSZ>;
defm : X86WriteResUnsupported<WriteCvtPS2PH>;
defm : X86WriteResUnsupported<WriteCvtPS2PHSt>;
defm : X86WriteResUnsupported<WriteCvtPS2PHY>;
defm : X86WriteResUnsupported<WriteCvtPS2PHZ>;
defm : X86WriteResUnsupported<WriteCvtPS2PHYSt>;
defm : X86WriteResUnsupported<WriteCvtPS2PHZSt>;

////////////////////////////////////////////////////////////////////////////////
// Vector integer operations.
////////////////////////////////////////////////////////////////////////////////

def  : WriteRes<WriteVecLoad,         [AtomPort0]>;
def  : WriteRes<WriteVecLoadX,        [AtomPort0]>;
defm : X86WriteResUnsupported<WriteVecLoadY>;
def  : WriteRes<WriteVecLoadNT,       [AtomPort0]>;
defm : X86WriteResUnsupported<WriteVecLoadNTY>;
defm : X86WriteResUnsupported<WriteVecMaskedLoad>;
defm : X86WriteResUnsupported<WriteVecMaskedLoadY>;

def  : WriteRes<WriteVecStore,        [AtomPort0]>;
def  : WriteRes<WriteVecStoreX,       [AtomPort0]>;
defm : X86WriteResUnsupported<WriteVecStoreY>;
def  : WriteRes<WriteVecStoreNT,      [AtomPort0]>;
defm : X86WriteResUnsupported<WriteVecStoreNTY>;
defm : X86WriteResUnsupported<WriteVecMaskedStore32>;
defm : X86WriteResUnsupported<WriteVecMaskedStore64>;
defm : X86WriteResUnsupported<WriteVecMaskedStore32Y>;
defm : X86WriteResUnsupported<WriteVecMaskedStore64Y>;

def  : WriteRes<WriteVecMove,          [AtomPort0]>;
def  : WriteRes<WriteVecMoveX,        [AtomPort01]>;
defm : X86WriteResUnsupported<WriteVecMoveY>;
defm : X86WriteResUnsupported<WriteVecMoveZ>;
defm : X86WriteRes<WriteVecMoveToGpr,   [AtomPort0], 3, [3], 1>;
defm : X86WriteRes<WriteVecMoveFromGpr, [AtomPort0], 1, [1], 1>;

defm : AtomWriteResPair<WriteVecALU,       [AtomPort01],  [AtomPort0], 1, 1>;
defm : AtomWriteResPair<WriteVecALUX,      [AtomPort01],  [AtomPort0], 1, 1>;
defm : X86WriteResPairUnsupported<WriteVecALUY>;
defm : X86WriteResPairUnsupported<WriteVecALUZ>;
defm : AtomWriteResPair<WriteVecLogic,     [AtomPort01],  [AtomPort0], 1, 1>;
defm : AtomWriteResPair<WriteVecLogicX,    [AtomPort01],  [AtomPort0], 1, 1>;
defm : X86WriteResPairUnsupported<WriteVecLogicY>;
defm : X86WriteResPairUnsupported<WriteVecLogicZ>;
defm : X86WriteResPairUnsupported<WriteVecTest>;
defm : X86WriteResPairUnsupported<WriteVecTestY>;
defm : X86WriteResPairUnsupported<WriteVecTestZ>;
defm : AtomWriteResPair<WriteVecShift,     [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 2, 3, [1,1], [2,2], 2, 3>;
defm : AtomWriteResPair<WriteVecShiftX,    [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 2, 3, [1,1], [2,2], 2, 3>;
defm : X86WriteResPairUnsupported<WriteVecShiftY>;
defm : X86WriteResPairUnsupported<WriteVecShiftZ>;
defm : AtomWriteResPair<WriteVecShiftImm,   [AtomPort0],  [AtomPort0], 1, 1>;
defm : AtomWriteResPair<WriteVecShiftImmX,  [AtomPort0],  [AtomPort0], 1, 1>;
defm : X86WriteResPairUnsupported<WriteVecShiftImmY>;
defm : X86WriteResPairUnsupported<WriteVecShiftImmZ>;
defm : AtomWriteResPair<WriteVecIMul,       [AtomPort0],  [AtomPort0], 4, 4, [1], [1]>;
defm : AtomWriteResPair<WriteVecIMulX,      [AtomPort0],  [AtomPort0], 5, 5, [2], [2]>;
defm : X86WriteResPairUnsupported<WriteVecIMulY>;
defm : X86WriteResPairUnsupported<WriteVecIMulZ>;
defm : X86WriteResPairUnsupported<WritePMULLD>;
defm : X86WriteResPairUnsupported<WritePMULLDY>;
defm : X86WriteResPairUnsupported<WritePMULLDZ>;
defm : X86WriteResPairUnsupported<WritePHMINPOS>;
defm : X86WriteResPairUnsupported<WriteMPSAD>;
defm : X86WriteResPairUnsupported<WriteMPSADY>;
defm : X86WriteResPairUnsupported<WriteMPSADZ>;
defm : AtomWriteResPair<WritePSADBW,        [AtomPort0],  [AtomPort0], 4, 4, [1], [1]>;
defm : AtomWriteResPair<WritePSADBWX,       [AtomPort0],  [AtomPort0], 5, 5, [2], [2]>;
defm : X86WriteResPairUnsupported<WritePSADBWY>;
defm : X86WriteResPairUnsupported<WritePSADBWZ>;
defm : AtomWriteResPair<WriteShuffle,       [AtomPort0],  [AtomPort0], 1, 1>;
defm : AtomWriteResPair<WriteShuffleX,      [AtomPort0],  [AtomPort0], 1, 1>;
defm : X86WriteResPairUnsupported<WriteShuffleY>;
defm : X86WriteResPairUnsupported<WriteShuffleZ>;
defm : AtomWriteResPair<WriteVarShuffle,    [AtomPort0],  [AtomPort0], 1, 1>;
defm : AtomWriteResPair<WriteVarShuffleX,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 4, 5, [3,3], [4,4], 4, 5>;
defm : X86WriteResPairUnsupported<WriteVarShuffleY>;
defm : X86WriteResPairUnsupported<WriteVarShuffleZ>;
defm : X86WriteResPairUnsupported<WriteBlend>;
defm : X86WriteResPairUnsupported<WriteBlendY>;
defm : X86WriteResPairUnsupported<WriteBlendZ>;
defm : X86WriteResPairUnsupported<WriteVarBlend>;
defm : X86WriteResPairUnsupported<WriteVarBlendY>;
defm : X86WriteResPairUnsupported<WriteVarBlendZ>;
defm : X86WriteResPairUnsupported<WriteShuffle256>;
defm : X86WriteResPairUnsupported<WriteVPMOV256>;
defm : X86WriteResPairUnsupported<WriteVarShuffle256>;
defm : X86WriteResPairUnsupported<WriteVarVecShift>;
defm : X86WriteResPairUnsupported<WriteVarVecShiftY>;
defm : X86WriteResPairUnsupported<WriteVarVecShiftZ>;

////////////////////////////////////////////////////////////////////////////////
// Vector insert/extract operations.
////////////////////////////////////////////////////////////////////////////////

defm : AtomWriteResPair<WriteVecInsert,     [AtomPort0],  [AtomPort0], 1, 1>;
def  : WriteRes<WriteVecExtract,   [AtomPort0]>;
def  : WriteRes<WriteVecExtractSt, [AtomPort0]>;

////////////////////////////////////////////////////////////////////////////////
// SSE42 String instructions.
////////////////////////////////////////////////////////////////////////////////

defm : X86WriteResPairUnsupported<WritePCmpIStrI>;
defm : X86WriteResPairUnsupported<WritePCmpIStrM>;
defm : X86WriteResPairUnsupported<WritePCmpEStrI>;
defm : X86WriteResPairUnsupported<WritePCmpEStrM>;

////////////////////////////////////////////////////////////////////////////////
// MOVMSK Instructions.
////////////////////////////////////////////////////////////////////////////////

def  : WriteRes<WriteFMOVMSK,    [AtomPort0]> { let Latency = 3; let ResourceCycles = [3]; }
def  : WriteRes<WriteVecMOVMSK,  [AtomPort0]> { let Latency = 3; let ResourceCycles = [3]; }
defm : X86WriteResUnsupported<WriteVecMOVMSKY>;
def  : WriteRes<WriteMMXMOVMSK,  [AtomPort0]> { let Latency = 3; let ResourceCycles = [3]; }

////////////////////////////////////////////////////////////////////////////////
// AES instructions.
////////////////////////////////////////////////////////////////////////////////

defm : X86WriteResPairUnsupported<WriteAESIMC>;
defm : X86WriteResPairUnsupported<WriteAESKeyGen>;
defm : X86WriteResPairUnsupported<WriteAESDecEnc>;

////////////////////////////////////////////////////////////////////////////////
// Horizontal add/sub  instructions.
////////////////////////////////////////////////////////////////////////////////

defm : AtomWriteResPair<WriteFHAdd,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 8, 9, [8,8], [9,9], 5, 6>;
defm : X86WriteResPairUnsupported<WriteFHAddY>;
defm : AtomWriteResPair<WritePHAdd,  [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 3, 4, [3,3], [4,4], 3, 4>;
defm : AtomWriteResPair<WritePHAddX, [AtomPort0,AtomPort1], [AtomPort0,AtomPort1], 7, 8, [7,7], [8,8], 3, 4>;
defm : X86WriteResPairUnsupported<WritePHAddY>;

////////////////////////////////////////////////////////////////////////////////
// Carry-less multiplication instructions.
////////////////////////////////////////////////////////////////////////////////

defm : X86WriteResPairUnsupported<WriteCLMul>;

////////////////////////////////////////////////////////////////////////////////
// Load/store MXCSR.
////////////////////////////////////////////////////////////////////////////////

defm : X86WriteRes<WriteLDMXCSR, [AtomPort0,AtomPort1],  5,   [5,5], 4>;
defm : X86WriteRes<WriteSTMXCSR, [AtomPort0,AtomPort1], 15, [15,15], 4>;

////////////////////////////////////////////////////////////////////////////////
// Special Cases.
////////////////////////////////////////////////////////////////////////////////

// Port0
def AtomWrite0_1 : SchedWriteRes<[AtomPort0]> {
  let Latency = 1;
  let ResourceCycles = [1];
}
def : InstRW<[AtomWrite0_1], (instrs XAM_F, LD_Frr,
                                     MOVSX64rr32)>;
def : SchedAlias<WriteALURMW, AtomWrite0_1>;
def : SchedAlias<WriteADCRMW, AtomWrite0_1>;
def : InstRW<[AtomWrite0_1], (instregex "(RCL|RCR|ROL|ROR|SAR|SHL|SHR)(8|16|32|64)m",
                                        "MOV(S|Z)X(32|64)rr(8|8_NOREX|16)")>;

// Port1
def AtomWrite1_1 : SchedWriteRes<[AtomPort1]> {
  let Latency = 1;
  let ResourceCycles = [1];
}
def : InstRW<[AtomWrite1_1], (instrs FCOMPP)>;
def : InstRW<[AtomWrite1_1], (instregex "UCOM_F(P|PP)?r")>;

def AtomWrite1_5 : SchedWriteRes<[AtomPort1]> {
  let Latency = 5;
  let ResourceCycles = [5];
}
def : InstRW<[AtomWrite1_5], (instrs MMX_CVTPI2PSrr, MMX_CVTPI2PSrm,
                                     MMX_CVTPS2PIrr, MMX_CVTTPS2PIrr)>;

// Port0 and Port1
def AtomWrite0_1_1 : SchedWriteRes<[AtomPort0, AtomPort1]> {
  let Latency = 1;
  let ResourceCycles = [1, 1];
}
def : InstRW<[AtomWrite0_1_1], (instrs POP32r, POP64r,
                                       POP16rmr, POP32rmr, POP64rmr,
                                       PUSH16r, PUSH32r, PUSH64r,
                                       PUSHi16, PUSHi32,
                                       PUSH16rmr, PUSH32rmr, PUSH64rmr,
                                       PUSH16i8, PUSH32i8, PUSH64i8, PUSH64i32,
                                       XCH_F)>;
def : InstRW<[AtomWrite0_1_1], (instregex "RETI(16|32|64)$",
                                          "IRET(16|32|64)?")>;

def AtomWrite0_1_5 : SchedWriteRes<[AtomPort0, AtomPort1]> {
  let Latency = 5;
  let ResourceCycles = [5, 5];
}
def : InstRW<[AtomWrite0_1_5], (instrs MMX_CVTPS2PIrm, MMX_CVTTPS2PIrm)>;
def : InstRW<[AtomWrite0_1_5], (instregex "ILD_F(16|32|64)")>;

def AtomWrite0_1_7 : SchedWriteRes<[AtomPort0,AtomPort1]> {
  let Latency = 7;
  let ResourceCycles = [6,6];
}
def : InstRW<[AtomWrite0_1_7], (instregex "CVTSI642SDrm(_Int)?")>;

def AtomWrite0_1_7_4 : SchedWriteRes<[AtomPort0,AtomPort1]> {
  let Latency = 7;
  let ResourceCycles = [8,8];
  let NumMicroOps = 4;
}
def : InstRW<[AtomWrite0_1_7_4], (instregex "CVTSI642SSrr(_Int)?")>;

def AtomWrite0_1_8_4 : SchedWriteRes<[AtomPort0,AtomPort1]> {
  let Latency = 8;
  let ResourceCycles = [8,8];
  let NumMicroOps = 4;
}
def : InstRW<[AtomWrite0_1_7_4], (instregex "CVTSI642SSrm(_Int)?")>;

def AtomWrite0_1_9 : SchedWriteRes<[AtomPort0,AtomPort1]> {
  let Latency = 9;
  let ResourceCycles = [9,9];
  let NumMicroOps = 4;
}
def : InstRW<[AtomWrite0_1_9], (instregex "CVT(T)?SS2SI64rr(_Int)?")>;

def AtomWrite0_1_10 : SchedWriteRes<[AtomPort0,AtomPort1]> {
  let Latency = 10;
  let ResourceCycles = [11,11];
  let NumMicroOps = 5;
}
def : InstRW<[AtomWrite0_1_10], (instregex "CVT(T)?SS2SI64rm(_Int)?")>;

// Port0 or Port1
def AtomWrite01_1 : SchedWriteRes<[AtomPort01]> {
  let Latency = 1;
  let ResourceCycles = [1];
}
def : InstRW<[AtomWrite01_1], (instrs FDECSTP, FFREE, FFREEP, FINCSTP, WAIT,
                                      LFENCE,
                                      STOSB, STOSL, STOSQ, STOSW,
                                      MOVSSrr, MOVSSrr_REV)>;

def AtomWrite01_2 : SchedWriteRes<[AtomPort01]> {
  let Latency = 2;
  let ResourceCycles = [2];
}
def : InstRW<[AtomWrite01_2], (instrs LEAVE, LEAVE64, POP16r,
                                      PUSH16rmm, PUSH32rmm, PUSH64rmm,
                                      LODSB, LODSL, LODSQ, LODSW,
                                      SCASB, SCASL, SCASQ, SCASW)>;
def : InstRW<[AtomWrite01_2], (instregex "PUSH(CS|DS|ES|FS|GS|SS)(16|32|64)",
                                         "(ST|ISTT)_F(P)?(16|32|64)?(m|rr)",
                                         "MMX_P(ADD|SUB)Qrr",
                                         "MOV(S|Z)X16rr8",
                                         "MOV(UPS|UPD|DQU)mr",
                                         "MASKMOVDQU(64)?",
                                         "P(ADD|SUB)Qrr")>;
def : SchedAlias<WriteBitTestSetImmRMW, AtomWrite01_2>;

def AtomWrite01_3 : SchedWriteRes<[AtomPort01]> {
  let Latency = 3;
  let ResourceCycles = [3];
}
def : InstRW<[AtomWrite01_3], (instrs CLD, LDDQUrm,
                                      CMPSB, CMPSL, CMPSQ, CMPSW,
                                      MOVSB, MOVSL, MOVSQ, MOVSW,
                                      POP16rmm, POP32rmm, POP64rmm)>;
def : InstRW<[AtomWrite01_3], (instregex "XADD(8|16|32|64)rm",
                                         "XCHG(8|16|32|64)rm",
                                         "PH(ADD|SUB)Drr",
                                         "MOV(S|Z)X16rm8",
                                         "MMX_P(ADD|SUB)Qrm",
                                         "MOV(UPS|UPD|DQU)rm",
                                         "P(ADD|SUB)Qrm")>;

def AtomWrite01_4 : SchedWriteRes<[AtomPort01]> {
  let Latency = 4;
  let ResourceCycles = [4];
}
def : InstRW<[AtomWrite01_4], (instrs CBW, CWD, CWDE, CDQ, CDQE, CQO,
                                      JCXZ, JECXZ, JRCXZ,
                                      LD_F80m)>;
def : InstRW<[AtomWrite01_4], (instregex "PH(ADD|SUB)Drm",
                                         "(MMX_)?PEXTRWrr(_REV)?")>;

def AtomWrite01_5 : SchedWriteRes<[AtomPort01]> {
  let Latency = 5;
  let ResourceCycles = [5];
}
def : InstRW<[AtomWrite01_5], (instrs FLDCW16m, ST_FP80m)>;
def : InstRW<[AtomWrite01_5], (instregex "MMX_PH(ADD|SUB)S?Wrr")>;

def AtomWrite01_6 : SchedWriteRes<[AtomPort01]> {
  let Latency = 6;
  let ResourceCycles = [6];
}
def : InstRW<[AtomWrite01_6], (instrs CMPXCHG8rm, INTO, XLAT,
                                      SHLD16rrCL, SHRD16rrCL,
                                      SHLD16rri8, SHRD16rri8,
                                      SHLD16mrCL, SHRD16mrCL,
                                      SHLD16mri8, SHRD16mri8)>;
def : InstRW<[AtomWrite01_6], (instregex "IST_F(P)?(16|32|64)?m",
                                         "MMX_PH(ADD|SUB)S?Wrm")>;

def AtomWrite01_7 : SchedWriteRes<[AtomPort01]> {
  let Latency = 7;
  let ResourceCycles = [7];
}
def : InstRW<[AtomWrite01_7], (instrs AAD8i8)>;

def AtomWrite01_8 : SchedWriteRes<[AtomPort01]> {
  let Latency = 8;
  let ResourceCycles = [8];
}
def : InstRW<[AtomWrite01_8], (instrs LOOPE,
                                      PUSHA16, PUSHA32,
                                      SHLD64rrCL, SHRD64rrCL,
                                      FNSTCW16m)>;

def AtomWrite01_9 : SchedWriteRes<[AtomPort01]> {
  let Latency = 9;
  let ResourceCycles = [9];
}
def : InstRW<[AtomWrite01_9], (instrs POPA16, POPA32,
                                      PUSHF16, PUSHF32, PUSHF64,
                                      SHLD64mrCL, SHRD64mrCL,
                                      SHLD64mri8, SHRD64mri8,
                                      SHLD64rri8, SHRD64rri8,
                                      CMPXCHG8rr)>;
def : InstRW<[AtomWrite01_9], (instregex "(U)?COM_FI", "TST_F")>;

def AtomWrite01_10 : SchedWriteRes<[AtomPort01]> {
  let Latency = 10;
  let ResourceCycles = [10];
}
def : SchedAlias<WriteFLDC, AtomWrite01_10>;

def AtomWrite01_11 : SchedWriteRes<[AtomPort01]> {
  let Latency = 11;
  let ResourceCycles = [11];
}
def : InstRW<[AtomWrite01_11], (instrs BOUNDS16rm, BOUNDS32rm)>;
def : SchedAlias<WriteBitTestSetRegRMW, AtomWrite01_11>;

def AtomWrite01_13 : SchedWriteRes<[AtomPort01]> {
  let Latency = 13;
  let ResourceCycles = [13];
}
def : InstRW<[AtomWrite01_13], (instrs AAA, AAS)>;

def AtomWrite01_14 : SchedWriteRes<[AtomPort01]> {
  let Latency = 14;
  let ResourceCycles = [14];
}
def : InstRW<[AtomWrite01_14], (instrs CMPXCHG16rm, CMPXCHG32rm, CMPXCHG64rm)>;

def AtomWrite01_17 : SchedWriteRes<[AtomPort01]> {
  let Latency = 17;
  let ResourceCycles = [17];
}
def : InstRW<[AtomWrite01_17], (instrs LOOPNE, PAUSE)>;

def AtomWrite01_18 : SchedWriteRes<[AtomPort01]> {
  let Latency = 18;
  let ResourceCycles = [18];
}
def : InstRW<[AtomWrite01_18], (instrs CMPXCHG8B, DAA, LOOP)>;

def AtomWrite01_20 : SchedWriteRes<[AtomPort01]> {
  let Latency = 20;
  let ResourceCycles = [20];
}
def : InstRW<[AtomWrite01_20], (instrs DAS)>;

def AtomWrite01_21 : SchedWriteRes<[AtomPort01]> {
  let Latency = 21;
  let ResourceCycles = [21];
}
def : InstRW<[AtomWrite01_21], (instrs AAM8i8, STD)>;

def AtomWrite01_22 : SchedWriteRes<[AtomPort01]> {
  let Latency = 22;
  let ResourceCycles = [22];
}
def : InstRW<[AtomWrite01_22], (instrs CMPXCHG16B)>;

def AtomWrite01_23 : SchedWriteRes<[AtomPort01]> {
  let Latency = 23;
  let ResourceCycles = [23];
}
def : InstRW<[AtomWrite01_23], (instrs ARPL16mr, ARPL16rr)>;

def AtomWrite01_25 : SchedWriteRes<[AtomPort01]> {
  let Latency = 25;
  let ResourceCycles = [25];
}
def : InstRW<[AtomWrite01_25], (instrs FNCLEX, FXTRACT)>;

def AtomWrite01_26 : SchedWriteRes<[AtomPort01]> {
  let Latency = 26;
  let ResourceCycles = [26];
}
def : InstRW<[AtomWrite01_26], (instrs POPF32, POPF64)>;

def AtomWrite01_29 : SchedWriteRes<[AtomPort01]> {
  let Latency = 29;
  let ResourceCycles = [29];
}
def : InstRW<[AtomWrite01_29], (instregex "POP(DS|ES|FS|GS)(16|32|64)")>;

def AtomWrite01_30 : SchedWriteRes<[AtomPort01]> {
  let Latency = 30;
  let ResourceCycles = [30];
}
def : InstRW<[AtomWrite01_30], (instrs RDTSC, RDTSCP)>;

def AtomWrite01_32 : SchedWriteRes<[AtomPort01]> {
  let Latency = 32;
  let ResourceCycles = [32];
}
def : InstRW<[AtomWrite01_32], (instrs ENTER, POPF16)>;

def AtomWrite01_45 : SchedWriteRes<[AtomPort01]> {
  let Latency = 45;
  let ResourceCycles = [45];
}
def : InstRW<[AtomWrite01_45], (instrs MONITOR32rrr, MONITOR64rrr)>;

def AtomWrite01_46 : SchedWriteRes<[AtomPort01]> {
  let Latency = 46;
  let ResourceCycles = [46];
}
def : InstRW<[AtomWrite01_46], (instrs FRNDINT, MWAITrr, RDPMC)>;

def AtomWrite01_48 : SchedWriteRes<[AtomPort01]> {
  let Latency = 48;
  let ResourceCycles = [48];
}
def : InstRW<[AtomWrite01_48], (instrs POPSS16, POPSS32)>;

def AtomWrite01_55 : SchedWriteRes<[AtomPort01]> {
  let Latency = 55;
  let ResourceCycles = [55];
}
def : InstRW<[AtomWrite01_55], (instrs FPREM)>;

def AtomWrite01_59 : SchedWriteRes<[AtomPort01]> {
  let Latency = 59;
  let ResourceCycles = [59];
}
def : InstRW<[AtomWrite01_59], (instrs INSB, INSL, INSW)>;

def AtomWrite01_63 : SchedWriteRes<[AtomPort01]> {
  let Latency = 63;
  let ResourceCycles = [63];
}
def : InstRW<[AtomWrite01_63], (instrs FNINIT)>;

def AtomWrite01_68 : SchedWriteRes<[AtomPort01]> {
  let Latency = 68;
  let ResourceCycles = [68];
}
def : InstRW<[AtomWrite01_68], (instrs OUT8rr, OUT16rr, OUT32rr)>;

def AtomWrite01_71 : SchedWriteRes<[AtomPort01]> {
  let Latency = 71;
  let ResourceCycles = [71];
}
def : InstRW<[AtomWrite01_71], (instrs FPREM1,
                                       INVLPG, INVLPGA32, INVLPGA64)>;

def AtomWrite01_72 : SchedWriteRes<[AtomPort01]> {
  let Latency = 72;
  let ResourceCycles = [72];
}
def : InstRW<[AtomWrite01_72], (instrs OUT8ir, OUT16ir, OUT32ir)>;

def AtomWrite01_74 : SchedWriteRes<[AtomPort01]> {
  let Latency = 74;
  let ResourceCycles = [74];
}
def : InstRW<[AtomWrite01_74], (instrs OUTSB, OUTSL, OUTSW)>;

def AtomWrite01_77 : SchedWriteRes<[AtomPort01]> {
  let Latency = 77;
  let ResourceCycles = [77];
}
def : InstRW<[AtomWrite01_77], (instrs FSCALE)>;

def AtomWrite01_78 : SchedWriteRes<[AtomPort01]> {
  let Latency = 78;
  let ResourceCycles = [78];
}
def : InstRW<[AtomWrite01_78], (instrs RDMSR)>;

def AtomWrite01_79 : SchedWriteRes<[AtomPort01]> {
  let Latency = 79;
  let ResourceCycles = [79];
}
def : InstRW<[AtomWrite01_79], (instregex "RET(16|32|64)?$",
                                          "LRETI?(16|32|64)")>;

def AtomWrite01_92 : SchedWriteRes<[AtomPort01]> {
  let Latency = 92;
  let ResourceCycles = [92];
}
def : InstRW<[AtomWrite01_92], (instrs IN8ri, IN16ri, IN32ri)>;

def AtomWrite01_94 : SchedWriteRes<[AtomPort01]> {
  let Latency = 94;
  let ResourceCycles = [94];
}
def : InstRW<[AtomWrite01_94], (instrs IN8rr, IN16rr, IN32rr)>;

def AtomWrite01_99 : SchedWriteRes<[AtomPort01]> {
  let Latency = 99;
  let ResourceCycles = [99];
}
def : InstRW<[AtomWrite01_99], (instrs F2XM1)>;

def AtomWrite01_121 : SchedWriteRes<[AtomPort01]> {
  let Latency = 121;
  let ResourceCycles = [121];
}
def : InstRW<[AtomWrite01_121], (instrs CPUID)>;

def AtomWrite01_127 : SchedWriteRes<[AtomPort01]> {
  let Latency = 127;
  let ResourceCycles = [127];
}
def : InstRW<[AtomWrite01_127], (instrs INT)>;

def AtomWrite01_130 : SchedWriteRes<[AtomPort01]> {
  let Latency = 130;
  let ResourceCycles = [130];
}
def : InstRW<[AtomWrite01_130], (instrs INT3)>;

def AtomWrite01_140 : SchedWriteRes<[AtomPort01]> {
  let Latency = 140;
  let ResourceCycles = [140];
}
def : InstRW<[AtomWrite01_140], (instrs FXSAVE, FXSAVE64)>;

def AtomWrite01_141 : SchedWriteRes<[AtomPort01]> {
  let Latency = 141;
  let ResourceCycles = [141];
}
def : InstRW<[AtomWrite01_141], (instrs FXRSTOR, FXRSTOR64)>;

def AtomWrite01_146 : SchedWriteRes<[AtomPort01]> {
  let Latency = 146;
  let ResourceCycles = [146];
}
def : InstRW<[AtomWrite01_146], (instrs FYL2X)>;

def AtomWrite01_147 : SchedWriteRes<[AtomPort01]> {
  let Latency = 147;
  let ResourceCycles = [147];
}
def : InstRW<[AtomWrite01_147], (instrs FYL2XP1)>;

def AtomWrite01_168 : SchedWriteRes<[AtomPort01]> {
  let Latency = 168;
  let ResourceCycles = [168];
}
def : InstRW<[AtomWrite01_168], (instrs FPTAN)>;

def AtomWrite01_174 : SchedWriteRes<[AtomPort01]> {
  let Latency = 174;
  let ResourceCycles = [174];
}
def : InstRW<[AtomWrite01_174], (instrs FSINCOS, FSIN, FCOS)>;

def AtomWrite01_183 : SchedWriteRes<[AtomPort01]> {
  let Latency = 183;
  let ResourceCycles = [183];
}
def : InstRW<[AtomWrite01_183], (instrs FPATAN)>;

def AtomWrite01_202 : SchedWriteRes<[AtomPort01]> {
  let Latency = 202;
  let ResourceCycles = [202];
}
def : InstRW<[AtomWrite01_202], (instrs WRMSR)>;

} // SchedModel
