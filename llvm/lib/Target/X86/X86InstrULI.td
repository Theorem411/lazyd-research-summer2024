//===-- X86InstrULI.td - ULI Extensions ----*- tablegen -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file describes the ULI related instructions
//
//===----------------------------------------------------------------------===//
//let Uses = [RAX, RCX] in

let hasNoSchedulingInfo = 1 in
{

def ULISEND   : I   <0x3e, MRMSrcReg, (outs), (ins GR64:$src0, GR64:$src1),
                               "ulisend\t{$src0, $src1}",
                           []>, TB, Requires<[In64BitMode]>;

def ULISENDN   : PseudoI<(outs), (ins GR64:$src0, GR64:$src1, GR32:$src2),
                   [(int_uli_send0cN GR64:$src0, GR64:$src1, GR32:$src2)]>;

def ULIREPLY   : I   <0x39, MRM2r, (outs), (ins GR64:$src0),
                                   "ulireply\t {$src0}",
                           []>, TB, Requires<[In64BitMode]>;

def ULIREPLYN   : PseudoI<(outs), (ins GR64:$src0, GR32:$src1),
                       [(int_uli_reply0cN GR64:$src0,GR32:$src1)]>;



def ULITOIREG   : I   <0x3c, MRMSrcReg, (outs), (ins GR32:$src0, GR64:$src1),
                                   "ulitoireg\t{$src0, $src1}",
                           [(int_uli_toireg GR32:$src0, GR64:$src1)]
                           >, TB, Requires<[In64BitMode]>;


def ULIFROMIREG : I <0x3b, MRMDestReg, (outs GR64:$dest), (ins GR32:$src),
                                   "ulifromireg\t{$src, $dest}",
                [(set GR64:$dest, (int_uli_fromireg GR32:$src))]
                >, TB, Requires<[In64BitMode]>;

// old definition
// dest and src registers are the same for this instruction.  Not sure how to specify
//let Constraints = "$src = $dest" in {
//def ULIFROMIREG   : I   <0x3b, MRM2r, (outs GR64:$dest), (ins GR64:$src),
//                                   "ulifromireg\t$dest",
//                [(set GR64:$dest, (int_x86_uli_fromireg GR64:$src))],
//                IIC_ALU_NONMEM>, TB, Requires<[In64BitMode]>;
//}


def GETCPU   : I   <0x3d, MRM2r, (outs GR32:$dest), (ins),
                                   "ulitoireg\t{$dest}",
                [(set GR32:$dest, (int_uli_getcpu))]
                >, TB, Requires<[In64BitMode]>;

// TB : Two bytes, don't use your instruction is one-byte opcode

// Enable uli mask,(based on replyuli)
def ULIENA   : I   <0x06, MRM2r, (outs), (ins GR64:$src0),
                                   "uliena\t{$src0}",
                [(int_uli_enable GR64:$src0)]
                >, OpSize32, Requires<[In64BitMode]>;

// Disable uli mask
def ULIDIS  : I <0x07, MRM2r, (outs), (ins GR64:$src0),
                                   "ulidis\t{$src0}",
                  [(int_uli_disable GR64:$src0)]
                  >, OpSize32, Requires<[In64BitMode]>;
// Based on POP
// Error: Primary decode conflict: ULIRD would overwrite PUSHSS32
def ULIRD : I<0x16, MRM2r, (outs GR64:$reg), (ins),
                           "ulird\t{$reg}",
                   [(set GR64:$reg, (int_uli_read))]
                   >, OpSize32, Requires<[In64BitMode]>;

// Write to register
def ULIWR : I <0x17, MRM2r, (outs), (ins GR64:$src0),
                               "uliwr\t{$src0}",
                 [(int_uli_set GR64:$src0)]
                 >, OpSize32, Requires<[In64BitMode]>;

// Set/Clear Atomic ULI
def ULIATOMIC : I <0x9A, MRM2r, (outs), (ins GR64:$src0),
                                "uliatomic\t{$src0}",
                [(int_uli_atomic GR64:$src0)]
                 >, OpSize32, Requires<[In64BitMode]>;

// Pop the ULI special register
def POPULIRDI : I<0xC5, MRM_D8, (outs), (ins),
                           "populirdi\t", []>, OpSize16, Requires<[In64BitMode]>;

def POPULIFLAGS : I<0xC5, MRM_D9, (outs), (ins),
                           "populiflags\t", []>, OpSize16, Requires<[In64BitMode]>;

def POPULINEXTPC : I<0xC5, MRM_DA, (outs), (ins),
                           "populinextpc\t", []>, OpSize16, Requires<[In64BitMode]>;

// Push the ULI special register
def PUSHULIRDI : I<0xC5, MRM_C8, (outs), (ins),
                           "pushulirdi\t", []>, OpSize16, Requires<[In64BitMode]>;

def PUSHULIFLAGS : I<0xC5, MRM_C9, (outs), (ins),
                           "pushuliflags\t", []>, OpSize16, Requires<[In64BitMode]>;

def PUSHULINEXTPC : I<0xC5, MRM_CA, (outs), (ins),
                           "pushulinextpc\t", []>, OpSize16, Requires<[In64BitMode]>;

// Read ULI special register
def ULIRDRDI : I<0x3E, MRM2r, (outs GR64:$reg), (ins),
                           "ulirdrdi\t{$reg}",
                   [(set GR64:$reg, (int_uli_rdrdi))]
                   >, OpSize32, Requires<[In64BitMode]>;

def ULIRDFLAGS : I<0x36, MRM2r, (outs GR64:$reg), (ins),
                           "ulirdflags\t{$reg}",
                   [(set GR64:$reg, (int_uli_rdflags))]
                   >, OpSize32, Requires<[In64BitMode]>;

def ULIRDRETADDR : I<0x26, MRM2r, (outs GR64:$reg), (ins),
                           "ulirdRA\t{$reg}",
                   [(set GR64:$reg, (int_uli_rdRA))]
                   >, OpSize32, Requires<[In64BitMode]>;

// Write ULI special register
def ULIWRRDI : I <0x3F, MRM2r, (outs), (ins GR64:$src0),
                               "uliwrrdi\t{$src0}",
                 [(int_uli_wrrdi GR64:$src0)]
                 >, OpSize32, Requires<[In64BitMode]>;

def ULIWRFLAGS : I <0x37, MRM2r, (outs), (ins GR64:$src0),
                               "uliwrflags\t{$src0}",
                 [(int_uli_wrflags GR64:$src0)]
                 >, OpSize32, Requires<[In64BitMode]>;


def ULIWRRETADDR : I <0x2F, MRM2r, (outs), (ins GR64:$src0),
                               "uliwrRA\t{$src0}",
                 [(int_uli_wrRA GR64:$src0)]
                 >, OpSize32, Requires<[In64BitMode]>;

// Support for Intel's UI
// Clear User Interrupt flag
// f3 0f 01 ec
// f3 0f  comes from XS
// 01 comes from <0x01
// ee comes from MRM_EC (Mod/RM byte)
def CLUI   : I   <0x01, MRM_EE, (outs), (ins),
                    "clui\t", [(int_x86_ui_clui)]>, XS, Requires<[In64BitMode]>;

def STUI   : I   <0x01, MRM_EF, (outs), (ins),
                    "stui\t", [(int_x86_ui_stui)]>, XS, Requires<[In64BitMode]>;

def TESTUI  : I  <0x01, MRM_ED, (outs), (ins),
                    "testui\t", [(int_x86_ui_testui)]>, XS, Requires<[In64BitMode]>;

def SENDUIPI  : I <0xC7, MRM6r, (outs), (ins GR64:$src0),
                    "senduipi\t{$src0} ", [(int_x86_ui_senduipi GR64:$src0)]>, XS, Requires<[In64BitMode]>;

}
//===----------------------------------------------------------------------===//
// Help stuff for stacklets

let usesCustomInserter = 1, isPseudo = 1, hasNoSchedulingInfo = 1, Uses = [RSP]
in {
   def READSP64 : PseudoI<(outs GR64:$dst), (ins),
                      [(set GR64:$dst, (int_x86_read_sp))]>,
                    Requires<[In64BitMode]>;
   def WRITESP64 : PseudoI<(outs), (ins GR64:$src),
                      [(int_x86_write_sp GR64:$src)]>,
                    Requires<[In64BitMode]>;

}

let isPseudo = 1, hasNoSchedulingInfo = 1
in {
   def GETFRAMESIZE : PseudoI<(outs GR64:$dst), (ins),
                      [(set GR64:$dst, (int_x86_get_frame_size))]>;
   def SETUP_RBP_FROM_RSP : PseudoI<(outs), (ins),
                      [(int_setup_rbp_from_rsp)]>;
   def SETUP_RSP_FROM_RBP : PseudoI<(outs), (ins),
                      [(int_setup_rsp_from_rbp)]>;
   def SETUP_RBP_FROM_SP_IN_RBP : PseudoI<(outs), (ins),
                      [(int_setup_rbp_from_sp_in_rbp)]>;
   def UI_DISABLE_REGION : PseudoI<(outs), (ins),
                      [(int_ui_disable_region)]>;
   def UI_ENABLE_REGION : PseudoI<(outs), (ins),
                      [(int_ui_enable_region)]>;
   def ULI_GET_WORKCONTEXT : PseudoI<(outs GR64:$dst), (ins),
                      [(set GR64:$dst, (int_uli_get_workcontext))]>;
   def ULI_CHILD_ADDRESSOFRETURNADDRESS : PseudoI<(outs GR64:$dst), (ins),
                      [(set GR64:$dst, (int_uli_child_addressofreturnaddress))]>;

 // TODO: Is this "Defs" needed for allow pseudo? How this should affect the lowering of thses pseudos?
 //let Uses = [R10, R11], hasSideEffects = 1, mayStore =  1, SchedRW = [WriteSystem], isBarrier = 1, isTerminator = 1 in
 //let Defs = [R10, R11, R12, R13, R14, R15, RBX], Uses = [R10, R11], hasSideEffects = 1, mayStore =  1, SchedRW = [WriteSystem], isBarrier = 1, isTerminator = 1 in
 let Defs = [R10, R11], Uses = [R10, R11], hasSideEffects = 1, mayStore =  1, SchedRW = [WriteSystem], isBarrier = 1, isTerminator = 1 in
 {
   def ULI_SAVE_CONTEXT : PseudoI<(outs), (ins),
      [(int_uli_save_context R10, R11)]>;
   def ULI_SAVE_CONTEXT_NOSP : PseudoI<(outs), (ins),
      [(int_uli_save_context_nosp R10, R11)]>;
 }

 let Uses = [R10, R11], hasSideEffects = 1, mayStore =  1, SchedRW = [WriteSystem], isBarrier = 1 in
 {
   def ULI_SAVE_CALLEE : PseudoI<(outs), (ins),
      [(int_uli_save_callee R10, R11)]>;
   def ULI_SAVE_CALLEE_NOSP : PseudoI<(outs), (ins),
      [(int_uli_save_callee_nosp R10, R11)]>;
 }


 //let Defs = [R10], Uses = [R10], hasSideEffects = 1, mayStore =  1, SchedRW = [WriteFence], isBarrier = 1, isTerminator = 1 in
 let Defs = [R10], Uses = [R10], hasSideEffects = 1, mayStore =  1, SchedRW = [WriteSystem], isBarrier = 1 in
 {
     def ULI_RESTORE_CONTEXT : PseudoI<(outs), (ins),
      [(int_uli_restore_context R10)]>;
     def ULI_RESTORE_CALLEE : PseudoI<(outs), (ins),
      [(int_uli_restore_callee R10)]>;

 }

}
