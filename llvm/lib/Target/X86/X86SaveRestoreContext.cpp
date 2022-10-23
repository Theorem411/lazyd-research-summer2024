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
#include "llvm/CodeGen/LivePhysRegs.h"
#include "llvm/CodeGen/WinEHFuncInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/Support/Debug.h"
#include "llvm/Target/TargetOptions.h"

#include <cstdlib>

// This files lower the save/restore context builtin into assembly

using namespace llvm;

#define X86_SAVERESTORE_CONTEXT_PASS_NAME "Save restore context"

namespace {

  class X86SaveRestoreContext : public MachineFunctionPass {
  public:
    static char ID;

    X86SaveRestoreContext() : MachineFunctionPass(ID) {
      initializeX86SaveRestoreContextPass(*PassRegistry::getPassRegistry());
    }

    bool runOnMachineFunction(MachineFunction &MF) override;

    StringRef getPassName() const override { return X86_SAVERESTORE_CONTEXT_PASS_NAME; }

  private:
    const unsigned I_RBP = 0;
    const unsigned I_RIP = 8;
    const unsigned I_RSP = 16;

    const unsigned I_RBX = 24; // 0
    const unsigned I_R12 = 32; // 1
    const unsigned I_R13 = 40; // 2
    const unsigned I_R14 = 48; // 3
    const unsigned I_R15 = 56; // 4
    const unsigned I_RDI = 64; // 5

    const unsigned I_RSI = 72;  // 6
    const unsigned I_R8 = 80;   // 7
    const unsigned I_R9 = 88;   // 8
    const unsigned I_R10 = 96;  // 9
    const unsigned I_R11 = 104; // 10
    const unsigned I_RDX = 112; // 11
    const unsigned I_RCX = 120; // 12
    const unsigned I_RAX = 128; // 13

    const unsigned I_BITVEC = 136;

  };

  char X86SaveRestoreContext::ID = 0;

  bool X86SaveRestoreContext::runOnMachineFunction(MachineFunction &MF) {
    const Function &Fn = MF.getFunction();
    const Module * M = Fn.getParent();
    const X86Subtarget &STI = MF.getSubtarget<X86Subtarget>();
    const X86RegisterInfo *TRI = STI.getRegisterInfo();
    const X86InstrInfo &TII = *STI.getInstrInfo();
    DebugLoc DL;
    unsigned StackPtr = TRI->getStackRegister();

    LivePhysRegs LiveRegs;
    SmallVector<MachineInstr *, 10> inst2delete;
    for (auto &MBB : MF) {
      // Code Inspired from StackMapLiveness
      LiveRegs.init(*TRI);
      // FIXME: This should probably be addLiveOuts().
      // Adds all live-out registers of basic block MBB but skips pristine registers. Pristine: registers not saved/restored?
      LiveRegs.addLiveOutsNoPristines(MBB);
      // Reverse iterate over all instructions and add the current live register
      // set to an instruction if we encounter a patchpoint instruction.
      for (auto I = MBB.rbegin(), E = MBB.rend(); I != E; ++I) {
	// Save context and callee
	if (I->getOpcode() == X86::ULI_SAVE_CONTEXT || I->getOpcode() == X86::ULI_SAVE_CONTEXT_NOSP) {
	  // Generate assembly for ULI_SAVE_CONTEXT/(_NOSP)
#if 0
	  uint32_t *Mask = MF.allocateRegisterMask(TRI->getNumRegs());
	  for (auto Reg : LiveRegs)
	    Mask[Reg / 32] |= 1U << (Reg % 32);

	  MachineOperand MO = MachineOperand::CreateRegLiveOut(Mask);
	  I->addOperand(MF, MO);
#endif


#if 0
	  MO.dump();
	  I->dump();
	  I->getOperand(0).dump();
	  I->getOperand(1).dump();
	  outs() << "   " << LiveRegs << "   " << *I << " Number of register: " << TRI->getNumRegs() << "Mask: " << Mask << "\n";
#endif
	  // Store base pointer
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RBP).addReg(X86::RBP);

	  // Store stack pointer
	  if (I->getOpcode() == X86::ULI_SAVE_CONTEXT) {
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RSP).addReg(X86::RSP);
	  }

	  // Store the second argument (IP) into the first argument + offset
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RIP).addReg(I->getOperand(1).getReg());

	  unsigned liveReg = 0;

	  // FIXME: If 32 bits, use mov32mr
	  // Store live register
	  for (auto Reg : LiveRegs)
	  {
	    if(false) {
	    //if(!(liveReg & 0x1) && (Reg == X86::RBX || Reg == X86::EBX || Reg == X86::BX || Reg == X86::BH || Reg == X86::BL)) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RBX).addReg(X86::RBX);
	      liveReg |= 0x1;
	    } else if(false) {
	    //} else if(!(liveReg & 0x2) &&(Reg == X86::R12 || Reg == X86::R12D || Reg == X86::R12W || Reg == X86::R12B)) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R12).addReg(X86::R12);
	      liveReg |= 0x2;
	    } else if(false) {
            //} else if(!(liveReg & 0x4) && (Reg == X86::R13 || Reg == X86::R13D || Reg == X86::R13W || Reg == X86::R13B) ) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R13).addReg(X86::R13);
	      liveReg |= 0x4;
	    } else if(false) {
            //} else if(!(liveReg & 0x8) &&(Reg == X86::R14 || Reg == X86::R14D || Reg == X86::R14W || Reg == X86::R14B) ) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R14).addReg(X86::R14);
	      liveReg |= 0x8;
	    } else if(false) {
	    //} else if(!(liveReg & 0x10) &&(Reg == X86::R15 || Reg == X86::R15D || Reg == X86::R15W || Reg == X86::R15B) ) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R15).addReg(X86::R15);
	      liveReg |= 0x10;
	    } else if(!(liveReg & 0x20) &&(Reg == X86::RDI || Reg == X86::EDI || Reg == X86::DI || Reg == X86::DIL) ) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RDI).addReg(X86::RDI);
	      liveReg |= 0x20;
	    } else if(!(liveReg & 0x40) && (Reg == X86::RSI || Reg == X86::ESI || Reg == X86::SI || Reg == X86::SIL) ) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RSI).addReg(X86::RSI);
	      liveReg |= 0x40;
	    } else if(!(liveReg & 0x80) &&(Reg == X86::R8 || Reg == X86::R8D || Reg == X86::R8W || Reg == X86::R8B)) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R8).addReg(X86::R8);
	      liveReg |= 0x80;
	    } else if(!(liveReg & 0x100) && (Reg == X86::R9 || Reg == X86::R9D || Reg == X86::R9W || Reg == X86::R9B)) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R9).addReg(X86::R9);
	      liveReg |= 0x100;
	    } else if(!(liveReg & 0x200) &&(Reg == X86::R10 || Reg == X86::R10D || Reg == X86::R10W || Reg == X86::R10B)) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R10).addReg(X86::R10);
	      liveReg |= 0x200;
	    } else if(!(liveReg & 0x400) && (Reg == X86::R11 || Reg == X86::R11D || Reg == X86::R11W || Reg == X86::R11B)) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R11).addReg(X86::R11);
	      liveReg |= 0x400;
	    } else if(!(liveReg & 0x800) &&(Reg == X86::RDX || Reg == X86::EDX || Reg == X86::DX || Reg == X86::DH || Reg == X86::DL)) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RDX).addReg(X86::RDX);
	      liveReg |= 0x800;
	    } else if(!(liveReg & 0x1000) &&(Reg == X86::RCX || Reg == X86::ECX || Reg == X86::CX || Reg == X86::CH || Reg == X86::CL)) {
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RCX).addReg(X86::RCX);
	      liveReg |= 0x1000;
	    } else if(!(liveReg & 0x2000) &&(Reg == X86::RAX || Reg == X86::EAX || Reg == X86::AX || Reg == X86::AH || Reg == X86::AL)) {
	      // Move from register to memory
	      addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RAX).addReg(X86::RAX);
	      liveReg |= 0x2000;
	    }
	  }

#if 1
	  // TODO: Hack Fix me later:
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RBX).addReg(X86::RBX);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R12).addReg(X86::R12);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R13).addReg(X86::R13);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R14).addReg(X86::R14);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R15).addReg(X86::R15);
#endif

	  //addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mi32)), I->getOperand(0).getReg(), false, I_BITVEC).addImm(liveReg);

	  // Delete this instr.
	  inst2delete.push_back(&*I);

	} else if(I->getOpcode() == X86::ULI_RESTORE_CONTEXT) {
	  // Generate assembly for ULI_RESTORE_CONTEXT
	  auto regParam0 = I->getOperand(0).getReg();

	  if(regParam0 != X86::RBX)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::RBX), regParam0, false, I_RBX);
	  if(regParam0 != X86::R12)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R12), regParam0, false, I_R12);
	  if(regParam0 != X86::R13)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R13), regParam0, false, I_R13);
	  if(regParam0 != X86::R14)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R14), regParam0, false, I_R14);
	  if(regParam0 != X86::R15)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R15), regParam0, false, I_R15);
	  if(regParam0 != X86::RDI)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::RDI), regParam0, false, I_RDI);
	  if(regParam0 != X86::RSI)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::RSI), regParam0, false, I_RSI);
	  if(regParam0 != X86::R8)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R8), regParam0, false, I_R8);
	  if(regParam0 != X86::R9)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R9), regParam0, false, I_R9);
	  if(regParam0 != X86::R10)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R10), regParam0, false, I_R10);
	  if(regParam0 != X86::R11)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R11), regParam0, false, I_R11);
	  if(regParam0 != X86::RDX)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::RDX), regParam0, false, I_RDX);
	  if(regParam0 != X86::RCX)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::RCX), regParam0, false, I_RCX);
	  if(regParam0 != X86::RAX)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::RAX), regParam0, false, I_RAX);

	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::RSP), regParam0, false, I_RSP);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::RBP), regParam0, false, I_RBP);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::TAILJMPm64)), regParam0, false, I_RIP);
	  inst2delete.push_back(&*I);
	} else if (I->getOpcode() == X86::ULI_RESTORE_CALLEE) {
	  // Generate assembly for ULI_RESTORE_CALLEE
	  auto regParam0 = I->getOperand(0).getReg();
	  if(regParam0 != X86::RBX)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::RBX), regParam0, false, I_RBX);
	  if(regParam0 != X86::R12)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R12), regParam0, false, I_R12);
	  if(regParam0 != X86::R13)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R13), regParam0, false, I_R13);
	  if(regParam0 != X86::R14)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R14), regParam0, false, I_R14);
	  if(regParam0 != X86::R15)
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64rm), X86::R15), regParam0, false, I_R15);

	  inst2delete.push_back(&*I);
	} else if (I->getOpcode() == X86::ULI_SAVE_CALLEE || I->getOpcode() == X86::ULI_SAVE_CALLEE_NOSP) {
	  // Store base pointer
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RBP).addReg(X86::RBP);

	  if (I->getOpcode() == X86::ULI_SAVE_CALLEE) {
	    addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RSP).addReg(X86::RSP);
	  }
	  // Store the second argument (IP) into the first argument + offset
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RIP).addReg(I->getOperand(1).getReg());

	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_RBX).addReg(X86::RBX);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R12).addReg(X86::R12);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R13).addReg(X86::R13);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R14).addReg(X86::R14);
	  addRegOffset(BuildMI(MBB, &*I, DL, TII.get(X86::MOV64mr)), I->getOperand(0).getReg(), false, I_R15).addReg(X86::R15);

	  inst2delete.push_back(&*I);
	}
	/// Simulates liveness when stepping backwards over an instruction(bundle):
	/// Remove Defs, add uses. This is the recommended way of calculating liveness.
	LiveRegs.stepBackward(*I);
      }
    }

    bool changed = false;
    for(auto i: inst2delete) {
      i->eraseFromParent();
      changed = true;
    }

    return changed;
  }

} // end of anonymous namespace

INITIALIZE_PASS(X86SaveRestoreContext, "x86-saverestore-context",
                X86_SAVERESTORE_CONTEXT_PASS_NAME,
                true, // is CFG only?
                true  // is analysis?
                )

namespace llvm {

  FunctionPass *createX86SaveRestoreContext() { return new X86SaveRestoreContext(); }

}
