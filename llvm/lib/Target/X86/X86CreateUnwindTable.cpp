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

using namespace llvm;

#define X86_CREATE_UNWINDTABLE_PASS_NAME "Create Unwind Table"

namespace {

  class X86CreateUnwindTable : public MachineFunctionPass {
  public:
    static char ID;

    X86CreateUnwindTable() : MachineFunctionPass(ID) {
      initializeX86CreateUnwindTablePass(*PassRegistry::getPassRegistry());
    }

    bool runOnMachineFunction(MachineFunction &MF) override;

    StringRef getPassName() const override { return X86_CREATE_UNWINDTABLE_PASS_NAME; }
  };

  char X86CreateUnwindTable::ID = 0;

  bool X86CreateUnwindTable::runOnMachineFunction(MachineFunction &MF) {        
    const Function &Fn = MF.getFunction();
    const Module * M = Fn.getParent();
    const X86Subtarget &STI = MF.getSubtarget<X86Subtarget>();
    const X86RegisterInfo *TRI = STI.getRegisterInfo();
    const X86InstrInfo &TII = *STI.getInstrInfo();
    DebugLoc DL;        
    unsigned StackPtr = TRI->getStackRegister();

    MCSymbol *unwindLabel = nullptr;
    // Add label at the end of call function and unwind path entry
    SmallVector<MachineBasicBlock *, 10> SpawnMBBs;

    // Used to create a table that maps the 
    for( auto mb = MF.begin(); mb != MF.end(); ++mb ) {      
      SpawnMBBs.push_back(&*mb);
      // Add label to unwind path entry
      if( mb->isUnwindPathEntry() ) {
#if 1
	MachineBasicBlock::iterator ii = mb->begin();
	unwindLabel = MF.getLabel();             
	BuildMI(*mb, ii, DL, TII.get(TargetOpcode::EH_LABEL)).addSym(unwindLabel);
#else
	unwindLabel = mb->getSymbol();
#endif
      }
    }
    
    if(unwindLabel) {
      // Add label at the end of call function
      for (auto spawnMBB : SpawnMBBs) {
	for (MachineBasicBlock::iterator I = spawnMBB->end(), E = spawnMBB->begin();  I != E;) {
	  --I;
	  if (I->isCall()) {
	    MCSymbol *Label = MF.getLabel();             	  
	    auto nextInst = I;
	    BuildMI(*spawnMBB, ++nextInst, DL, TII.get(TargetOpcode::EH_LABEL)).addSym(Label);
	    // Use to generate the prehash table in the elf binary
	    MF.getContext().preHashTableEntry.push_back(std::make_pair(Label,unwindLabel));	    
	  }
	}
      }
      return true;
    }
    return false;
  }

} // end of anonymous namespace

INITIALIZE_PASS(X86CreateUnwindTable, "x86-create-unwindtable",
                X86_CREATE_UNWINDTABLE_PASS_NAME,
                true, // is CFG only?
                true  // is analysis?
                )

namespace llvm {

  FunctionPass *createX86CreateUnwindTable() { return new X86CreateUnwindTable(); }

}
