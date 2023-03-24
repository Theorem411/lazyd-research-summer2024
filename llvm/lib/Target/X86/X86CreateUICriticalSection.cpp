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

// Replace the X86::UI_DISABLE_REGION and X86::UI_ENABLE_REGION with a label.
// This create the UI critical section region
// The intended use is to disable and enable UI (create the critical section)
// TODO: Make sure the order intended by the programmer is not modified. 

using namespace llvm;

#define X86_CREATEUI_CRITICALSECTION_PASS_NAME "Create UI Critical Section"

namespace {

  class X86CreateUICriticalSection : public MachineFunctionPass {
  public:
    static char ID;

    X86CreateUICriticalSection() : MachineFunctionPass(ID) {
      initializeX86CreateUICriticalSectionPass(*PassRegistry::getPassRegistry());
    }

    bool runOnMachineFunction(MachineFunction &MF) override;

    StringRef getPassName() const override { return X86_CREATEUI_CRITICALSECTION_PASS_NAME; }
  };

  char X86CreateUICriticalSection::ID = 0;

  bool X86CreateUICriticalSection::runOnMachineFunction(MachineFunction &MF) {

    const Function &Fn = MF.getFunction();
    const Module * M = Fn.getParent();
    const X86Subtarget &STI = MF.getSubtarget<X86Subtarget>();
    const X86RegisterInfo *TRI = STI.getRegisterInfo();
    const X86InstrInfo &TII = *STI.getInstrInfo();
    DebugLoc DL;
    unsigned StackPtr = TRI->getStackRegister();

    bool changed = false;

    // Locate the ui_disable_region and ui_enable_region
    MachineInstr * ui_disable_region = nullptr;
    MachineInstr * ui_enable_region = nullptr;
    for (auto mb = MF.begin(); mb != MF.end(); ++mb) {
      for (auto inst = mb->begin(); inst != mb->end(); ++inst) {
	if (inst->getOpcode() == X86::UI_DISABLE_REGION) {
	  ui_disable_region = &*inst;
	} else if (inst->getOpcode() == X86::UI_ENABLE_REGION) {
	  ui_enable_region = &*inst;
	}
      }
    }

    if(ui_disable_region && ui_enable_region) {
      changed = true;

      // Replace it with a lable
      auto startLabel = MF.getLabel();
      BuildMI(*ui_disable_region->getParent(), ui_disable_region, DL, TII.get(TargetOpcode::EH_LABEL)).addSym(startLabel);

      auto endLabel = MF.getLabel();
      BuildMI(*ui_enable_region->getParent(), ui_enable_region, DL, TII.get(TargetOpcode::EH_LABEL)).addSym(endLabel);

      // Push start and end into prolog epilog table
      MF.getContext().prePrologEpilogEntry.push_back(std::make_pair(startLabel,endLabel));

      // Delete the instruction
      ui_disable_region->eraseFromParent();
      ui_enable_region->eraseFromParent();
    }

    return changed;
  }

} // end of anonymous namespace

INITIALIZE_PASS(X86CreateUICriticalSection, "x86-createui-criticalsection",
                X86_CREATEUI_CRITICALSECTION_PASS_NAME,
                true, // is CFG only?
                true  // is analysis?
                )

namespace llvm {

  FunctionPass *createX86CreateUICriticalSection() { return new X86CreateUICriticalSection(); }

}
