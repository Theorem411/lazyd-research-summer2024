#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"

#include "X86FrameLowering.h"
#include "X86InstrBuilder.h"
#include "X86InstrInfo.h"
#include "X86MachineFunctionInfo.h"
#include "X86Subtarget.h"
#include "X86TargetMachine.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Analysis/EHPersonalities.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/WinEHFuncInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/Support/Debug.h"
#include "llvm/Target/TargetOptions.h"

#include <cstdlib>

// This file contains the X86 implementation of clearing the return address to zero once it is used.
// Used in Seed Stack implementation


// Replace the return instruction
// '''
// RET
// '''
// with
// '''''''''''''''''''''''''''''
// mov rax, r8       // Saved rax to r8, since rax is used in CAS
// mov (rsp), rax    // Saved return address to rax
// xor rdx, rdx      // Store 0 to rdx
// cas rdx, (rsp)    // Peform CAS on the return address
// if true :         
// mov rax, rdx      // Store return address in rdx
// mov r8, rax       // Restore RAX
// rsp++             // Increment SP
// jmp *rdx          // Return
// else :
// mov (rsp), rdx    // Store new return address in rdx
// mov r8, rdx       // Restore RAX
// rsp++             // Increment SP
// jmp *rdx          // Return


using namespace llvm;

#define X86_CLEAR_RETURN_PASS_NAME "Clear Return Address"

namespace {

  class X86ClearReturn : public MachineFunctionPass {
  public:
    static char ID;

    X86ClearReturn() : MachineFunctionPass(ID) {
      initializeX86ClearReturnPass(*PassRegistry::getPassRegistry());
    }

    bool runOnMachineFunction(MachineFunction &MF) override;

    StringRef getPassName() const override { return X86_CLEAR_RETURN_PASS_NAME; }
  };

  char X86ClearReturn::ID = 0;

  bool X86ClearReturn::runOnMachineFunction(MachineFunction &MF) {
        
    //const TargetFrameLowering *TFI = MF.getSubtarget<X86Subtarget>().getFrameLowering();
    //bool Uses64BitFramePtr = STI.isTarget64BitLP64() || STI.isTargetNaCl64();
        
    const Function &Fn = MF.getFunction();
    const Module * M = Fn.getParent();
    const X86Subtarget &STI = MF.getSubtarget<X86Subtarget>();
    const X86RegisterInfo *TRI = STI.getRegisterInfo();
    const X86InstrInfo &TII = *STI.getInstrInfo();
    DebugLoc DL;        
    unsigned StackPtr = TRI->getStackRegister();

    bool changed = false;

    if ( Fn.hasFnAttribute(Attribute::Forkable) && M->getTapirTarget() == TapirTargetType::CAS ){
      changed = true;
      for (auto mb = MF.begin(); mb != MF.end(); ++mb) {
	for (auto inst = mb->begin(); inst != mb->end(); ++inst) {	  
	  if (inst->getOpcode() == X86::RET || inst->getOpcode() == X86::RETL || inst->getOpcode() == X86::RETQ) {
	    DL = inst->getDebugLoc();
                        
	    const BasicBlock *LLVM_BB =mb->getBasicBlock();
                        
	    // Copy from X86 Frame lowering, Create a basic block for when CAS succeed
	    MachineBasicBlock *CassuccMBB = MF.CreateMachineBasicBlock(LLVM_BB);
	    MachineFunction::iterator MBBIter = std::next(mb->getIterator());
	    MF.insert(MBBIter, CassuccMBB);

	    // Saved the return result since it RAX is used in CAS
	    // Saved in R8
#if 0                        
	    BuildMI(*mb, inst, DL, TII.get(X86::PUSH64r)).addReg(X86::RAX);
#else
	    BuildMI(*mb, inst, DL, TII.get(X86::MOV64rr), X86::R8).addReg(X86::RAX);
#endif
                       
	    // Saved the return address into RAX
#if 0
	    addRegOffset(BuildMI(*mb, inst, DL, TII.get(X86::MOV64rm), X86::RAX),  StackPtr, false, 8);
#else
	    addRegOffset(BuildMI(*mb, inst, DL, TII.get(X86::MOV64rm), X86::RAX),  StackPtr, false, 0);
#endif                        
                       
	    // Store 0 into RDX, used in CAS
	    BuildMI(*mb, inst, DL, TII.get(X86::XOR64rr), X86::RDX).addReg(X86::RDX).addReg(X86::RDX);

	    // Perform compare (return address with ras) and swap (return address and rdx)
#if 0                        
	    BuildMI(*mb, inst, DL, TII.get(X86::LCMPXCHG64)).addReg(StackPtr).addImm(1).addReg(0).addImm(8).addReg(0).addReg(X86::RDX);
#else
	    BuildMI(*mb, inst, DL, TII.get(X86::LCMPXCHG64)).addReg(StackPtr).addImm(1).addReg(0).addImm(0).addReg(0).addReg(X86::RDX);
#endif
                        
	    // Jump to CassuccMBB if cas suceed, else fall through
	    BuildMI(*mb, inst, DL, TII.get(X86::JE_1)).addMBB(CassuccMBB);

	    // If true, move return address to rdx
	    BuildMI(CassuccMBB, DL, TII.get(X86::MOV64rr), X86::RDX).addReg(X86::RAX);

	    // Restore original rax value
#if 0
	    BuildMI(CassuccMBB, DL, TII.get(X86::POP64r)).addReg(X86::RAX);
#else
	    BuildMI(CassuccMBB, DL, TII.get(X86::MOV64rr), X86::RAX).addReg(X86::R8);
#endif
	    // Increment SP
	    BuildMI(CassuccMBB, DL, TII.get(X86::ADD64ri8), StackPtr).addReg(StackPtr).addImm(8);
                        
	    // Jump to return address
	    BuildMI(CassuccMBB, DL, TII.get(X86::JMP64r)).addReg(X86::RDX);

	    //-------------------------------------------------------------
                        
	    // If fail, move new return address to rdx
#if 0
	    addRegOffset(BuildMI(*mb, inst, DL, TII.get(X86::MOV64rm), X86::RDX),  StackPtr, false, 8);
#else
	    addRegOffset(BuildMI(*mb, inst, DL, TII.get(X86::MOV64rm), X86::RDX),  StackPtr, false, 0);
#endif

	    // Restore original rax value
#if 0
	    BuildMI(*mb, inst, DL, TII.get(X86::POP64r)).addReg(X86::RAX);
#else
	    BuildMI(*mb, inst, DL, TII.get(X86::MOV64rr), X86::RAX).addReg(X86::R8);
#endif
                        
	    // Increment SP
	    BuildMI(*mb, inst, DL, TII.get(X86::ADD64ri8), StackPtr).addReg(StackPtr).addImm(8);
                        
	    // Jump to new return address
	    BuildMI(*mb, inst, DL, TII.get(X86::JMP64r)).addReg(X86::RDX);
                        
	    // Add Control flow
	    mb->addSuccessor(CassuccMBB);
                        
 
	  }
	}
      }
    }
    return changed;
  }

} // end of anonymous namespace

INITIALIZE_PASS(X86ClearReturn, "x86-clear-return",
                X86_CLEAR_RETURN_PASS_NAME,
                true, // is CFG only?
                true  // is analysis?
                )

namespace llvm {

  FunctionPass *createX86ClearReturn() { return new X86ClearReturn(); }

}
