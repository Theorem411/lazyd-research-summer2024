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


def ULISEND   : I   <0x3e, MRMSrcReg, (outs), (ins GR64:$src0, GR64:$src1),
                               "ulisend\t{$src0, $src1}",
                           [], IIC_ALU_NONMEM>, TB, Requires<[In64BitMode]>;

def ULISENDN   : PseudoI<(outs), (ins GR64:$src0, GR64:$src1, GR32:$src2),
                   [(int_x86_uli_send0cN GR64:$src0, GR64:$src1, GR32:$src2)]>;

def ULIREPLY   : I   <0x39, MRM2r, (outs), (ins GR64:$src0),
                                   "ulireply\t {$src0}",
                           [], IIC_ALU_NONMEM>, TB, Requires<[In64BitMode]>;

def ULIREPLYN   : PseudoI<(outs), (ins GR64:$src0, GR32:$src1),
                       [(int_x86_uli_reply0cN GR64:$src0,GR32:$src1)]>;



def ULITOIREG   : I   <0x3c, MRMSrcReg, (outs), (ins GR32:$src0, GR64:$src1),
                                   "ulitoireg\t{$src0, $src1}",
                           [(int_x86_uli_toireg GR32:$src0, GR64:$src1)],
                           IIC_ALU_NONMEM>, TB, Requires<[In64BitMode]>;


def ULIFROMIREG : I <0x3b, MRMDestReg, (outs GR64:$dest), (ins GR32:$src),
                                   "ulifromireg\t{$src, $dest}",
                [(set GR64:$dest, (int_x86_uli_fromireg GR32:$src))],
                IIC_ALU_NONMEM>, TB, Requires<[In64BitMode]>;

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
                [(set GR32:$dest, (int_x86_uli_getcpu))],
                IIC_ALU_NONMEM>, TB, Requires<[In64BitMode]>;

// TB : Two bytes, don't use your instruction is one-byte opcode

// Enable uli mask,(based on replyuli)
def ULIENA   : I   <0x06, MRM2r, (outs), (ins GR64:$src0),
                                   "uliena\t{$src0}",
                [(int_x86_uli_enable GR64:$src0)],
                IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;

// Disable uli mask
def ULIDIS  : I <0x07, MRM2r, (outs), (ins GR64:$src0),
                                   "ulidis\t{$src0}",
                  [(int_x86_uli_disable GR64:$src0)],
                  IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;
// Based on POP
// Error: Primary decode conflict: ULIRD would overwrite PUSHSS32
def ULIRD : I<0x16, MRM2r, (outs GR64:$reg), (ins),
                           "ulird\t{$reg}",
                   [(set GR64:$reg, (int_x86_uli_read))],
                   IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;

// Write to register
def ULIWR : I <0x17, MRM2r, (outs), (ins GR64:$src0),
                               "uliwr\t{$src0}",
                 [(int_x86_uli_set GR64:$src0)],
                 IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;

// Set/Clear Atomic ULI
def ULIATOMIC : I <0x9A, MRM2r, (outs), (ins GR64:$src0),
                                "uliatomic\t{$src0}",
                [(int_x86_uli_atomic GR64:$src0)],
                 IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;

// Pop the ULI special register
def POPULIRDI : I<0xC5, MRM_D8, (outs), (ins),
                           "populirdi\t", [], IIC_ALU_NONMEM>, OpSize16, Requires<[In64BitMode]>;

def POPULIFLAGS : I<0xC5, MRM_D9, (outs), (ins),
                           "populiflags\t", [], IIC_ALU_NONMEM>, OpSize16, Requires<[In64BitMode]>;

def POPULINEXTPC : I<0xC5, MRM_DA, (outs), (ins),
                           "populinextpc\t", [], IIC_ALU_NONMEM>, OpSize16, Requires<[In64BitMode]>;

// Push the ULI special register
def PUSHULIRDI : I<0xC5, MRM_C8, (outs), (ins),
                           "pushulirdi\t", [], IIC_ALU_NONMEM>, OpSize16, Requires<[In64BitMode]>;

def PUSHULIFLAGS : I<0xC5, MRM_C9, (outs), (ins),
                           "pushuliflags\t", [], IIC_ALU_NONMEM>, OpSize16, Requires<[In64BitMode]>;

def PUSHULINEXTPC : I<0xC5, MRM_CA, (outs), (ins),
                           "pushulinextpc\t", [], IIC_ALU_NONMEM>, OpSize16, Requires<[In64BitMode]>;

// Read ULI special register
def ULIRDRDI : I<0x3E, MRM2r, (outs GR64:$reg), (ins),
                           "ulirdrdi\t{$reg}",
                   [(set GR64:$reg, (int_x86_uli_rdrdi))],
                   IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;

def ULIRDFLAGS : I<0x36, MRM2r, (outs GR64:$reg), (ins),
                           "ulirdflags\t{$reg}",
                   [(set GR64:$reg, (int_x86_uli_rdflags))],
                   IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;

def ULIRDRETADDR : I<0x26, MRM2r, (outs GR64:$reg), (ins),
                           "ulirdRA\t{$reg}",
                   [(set GR64:$reg, (int_x86_uli_rdRA))],
                   IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;

// Write ULI special register
def ULIWRRDI : I <0x3F, MRM2r, (outs), (ins GR64:$src0),
                               "uliwrrdi\t{$src0}",
                 [(int_x86_uli_wrrdi GR64:$src0)],
                 IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;

def ULIWRFLAGS : I <0x37, MRM2r, (outs), (ins GR64:$src0),
                               "uliwrflags\t{$src0}",
                 [(int_x86_uli_wrflags GR64:$src0)],
                 IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;


def ULIWRRETADDR : I <0x2F, MRM2r, (outs), (ins GR64:$src0),
                               "uliwrRA\t{$src0}",
                 [(int_x86_uli_wrRA GR64:$src0)],
                 IIC_ALU_NONMEM>, OpSize32, Requires<[In64BitMode]>;


//===----------------------------------------------------------------------===//
// Help stuff for stacklets

let usesCustomInserter = 1, isPseudo = 1, Uses = [RSP]
in {
   def READSP64 : PseudoI<(outs GR64:$dst), (ins),
                      [(set GR64:$dst, (int_x86_read_sp))]>,
                    Requires<[In64BitMode]>;
}

let isPseudo = 1
in {
   def GETFRAMESIZE : PseudoI<(outs GR64:$dst), (ins),
                      [(set GR64:$dst, (int_x86_get_frame_size))]>;
   def SETUP_RBP_FROM_RSP : PseudoI<(outs), (ins),
                      [(int_x86_setup_rbp_from_rsp)]>;
   def SETUP_RSP_FROM_RBP : PseudoI<(outs), (ins),
                      [(int_x86_setup_rsp_from_rbp)]>;
   def SETUP_RBP_FROM_SP_IN_RBP : PseudoI<(outs), (ins),
                      [(int_x86_setup_rbp_from_sp_in_rbp)]>;
   def ULI_GET_WORKCONTEXT : PseudoI<(outs GR64:$dst), (ins),
                      [(set GR64:$dst, (int_x86_uli_get_workcontext))]>;
   def ULI_CHILD_ADDRESSOFRETURNADDRESS : PseudoI<(outs GR64:$dst), (ins),
                      [(set GR64:$dst, (int_x86_uli_child_addressofreturnaddress))]>;


 let Uses = [R10, R11] in		      
 {
   def ULI_SAVE_CONTEXT : PseudoI<(outs), (ins),
      [(int_x86_uli_save_context R10, R11)]>;
   def ULI_SAVE_CALLEE : PseudoI<(outs), (ins),
      [(int_x86_uli_save_callee R10, R11)]>;
   def ULI_SAVE_CONTEXT_NOSP : PseudoI<(outs), (ins),
      [(int_x86_uli_save_context_nosp R10, R11)]>;
 }

 let Uses = [R10] in 

 {    
     def ULI_RESTORE_CONTEXT : PseudoI<(outs), (ins),
      [(int_x86_uli_restore_context R10)]>; 
 }	

}
