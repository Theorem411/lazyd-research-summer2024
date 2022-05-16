#define DEBUG_TYPE "live-variable"

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

//#include "llvm/IR/PassManager.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Transforms/ULI/LazyLiveVariable.h"

using namespace llvm;
using namespace std;

//namespace llvm {


BitVector LiveVariable::unionFcn (std::vector<BitVector> &values) {
    assert(values.size() > 0);
    BitVector res = values[0];
    for (std::vector<BitVector>::iterator value = values.begin(); value != values.end(); ++value) {
      res |= *value;
    }
    return res;
}

BitVector LiveVariable::livenessTrans(BitVector &value, std::vector<BitVector> &genAndKill) {
  assert(genAndKill.size() == 2);
  BitVector gen = genAndKill[0];
  BitVector kill = genAndKill[1];
  value &= kill.flip(); // x - kill()
  value |= gen; // gen() U (x-kill())
  return value;
}

std::vector<BitVector>  LiveVariable::instGenAndKill(BitVector &value,  Instruction* I,   ValueMap<Instruction*, unsigned> &inst2idxMap) {
  static std::vector<BitVector> genAndKill;
  BitVector kill = BitVector(value.size(), false);
  BitVector gen = BitVector(value.size(), false);
    
  DEBUG (dbgs() << "\n---------- Instruction gen and kill ---------------\n");
  DEBUG (dbgs() << *I << "\n");

  // Get the uses
  if(isa<BranchInst>(I) ) {
    BranchInst* brInst = dyn_cast<BranchInst>(I);
    if(brInst->isConditional()) {
      Value* v = brInst->getCondition();
      Instruction * iv = dyn_cast<Instruction>(v);
      if( inst2idxMap.find(iv) != inst2idxMap.end() ) {
	int idx2gen = inst2idxMap[iv];
	gen.set(idx2gen);
	DEBUG (dbgs() << "Branch: Gen variable ["<< to_string(idx2gen) << "]: " << *iv << "\n");
      }
    }
  } else {
    
    // ---------------------------------------------------
    // Weird instruction can be filter out using the lookup
    if( inst2idxMap.find(I) != inst2idxMap.end() ) {
      int idx2kill = inst2idxMap[I];
      kill.set(idx2kill);
      DEBUG (dbgs() << "Kill variable ["<< to_string(idx2kill) << "]: " << *I << "\n");
    }   
    
    // Handle getelementptr and load inst
    
    for (Use &U : I->operands()) {
      Value *v = U.get();
      Instruction * iv = dyn_cast<Instruction>(v);
      if( inst2idxMap.find(iv) != inst2idxMap.end() ) {
	int idx2gen = inst2idxMap[iv];
	gen.set(idx2gen);
	DEBUG (dbgs() << "Gen variable ["<< to_string(idx2gen) << "]: " << *iv << "\n");
      }
    } 
    //---------------------------------------------------------
  }

  genAndKill.clear();
  genAndKill.push_back(gen);
  genAndKill.push_back(kill);
  
  return genAndKill;    
}

bool LiveVariable::ignoreInst(Instruction* I) {
  bool ignoreInst = isa<ReturnInst>(I) || isa<BranchInst>(I) || isa<DetachInst>(I) || 
    isa<SyncInst>(I) || isa<StoreInst>(I) || isa<LandingPadInst>(I) || isa<IndirectBrInst>(I) ||
    isa<IndirectBrInst>(I) || isa<LandingPadInst>(I)  || isa<UnreachableInst>(I) || isa<ResumeInst>(I) ||  isa<ReattachInst>(I); 
  
  if(isa<CallInst>(I)) {
    CallInst* ci = dyn_cast<CallInst>(I);
    ignoreInst = ci->getFunctionType()->getReturnType()->isVoidTy();
  }
  
  return ignoreInst;
}


void LiveVariable::recalculate(Function& F) {
  // Get the entry of the basic block
  BasicBlock* entry = &F.getEntryBlock();
  
  // Push the basic block in DFS order
  SmallVector<BasicBlock*, 4> bbList;
  SmallVector<BasicBlock*, 4> bbTraverse;
  SmallVector<BasicBlock*, 4> bbReverse;
  ValueMap<BasicBlock*, bool> haveVisited;
  ValueMap<BasicBlock*, BitVector> mapBB2LiveOutVal;
  ValueMap<BasicBlock*, DenseMap<BasicBlock*, BitVector>> mapBB2LiveInVal;
  
  unsigned idx = 0;
  ValueMap<Instruction*, unsigned> inst2idxMap;
  SmallVector<Instruction*, 4> idx2instMap;

  LivenessInMap.clear();
  
  // Create the order of updating the basic block
  // while initializing a few data structure
  BasicBlock* bb = nullptr;
  bbList.push_back(entry);
  while(!bbList.empty()) {
    bb = bbList.back();
    bbList.pop_back();
    if(haveVisited.lookup(bb)){
      continue;
    }

    // Perform some initialization on the basic block
    haveVisited[bb] = true;    
    bbTraverse.push_back(bb);
    
    // Create a map from basic block to idx
    for( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {                
      BasicBlock* succ = *SI;
      bbList.push_back(succ);
    }
  }

  // Create the map 
  DEBUG (dbgs() << "\n----Construct variable map-----\n");


  for (Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {
    BasicBlock *block = &*FI;
    
    for (BasicBlock::iterator i = block->begin(), e = block->end(); i != e; ++i) {
      Instruction *I = &*i;
      DEBUG (dbgs() << I << "\n");
      // Process inst. with assignment
      if (!ignoreInst(I)) {
	if (inst2idxMap.find(I) == inst2idxMap.end()) {
	  idx2instMap.push_back(I);
	  inst2idxMap[I] = idx;
	  idx++;
	  DEBUG (dbgs() << "Variable name : [" << to_string(idx-1) << "] " << *I << "\n");
	}
      }
      DEBUG (dbgs() << "***********\n");
    }
  }
  
  // Initialize the entry 
  BitVector initBound = BitVector(idx, false);
  BitVector initBB = BitVector(idx, false);
  
  for(auto pBB : bbTraverse) {
    mapBB2LiveOutVal[pBB] = initBB;
    // Due to phinode, the input the predecessor are different
    // Process phi node
    for (pred_iterator PI = pred_begin(pBB); PI != pred_end(pBB); PI++){	 
      mapBB2LiveInVal[pBB][*PI] = initBB;
    }

  }

  // Start performing the data flow analyze
  // if result is the same terminate
  
  bool bHaveChanged = true;
  while(bHaveChanged) {
    bHaveChanged = false;
    for (auto it = bbTraverse.rbegin() ; it != bbTraverse.rend() ; it++){
      BasicBlock* pBB = *it;
      BitVector bbOutput;
      BitVector bbOutputTmp;
      std::vector<BitVector> predBasicBlockValues;
      for( succ_iterator SI = succ_begin(pBB); SI != succ_end(pBB); SI++ ) {                
	BasicBlock* succ = *SI;
	predBasicBlockValues.push_back(mapBB2LiveInVal[succ][pBB]);
      }
      
      // If entry
      if(isa<ReturnInst>(pBB->getTerminator())) {
	predBasicBlockValues.push_back(initBound);
      } 

      if(!predBasicBlockValues.empty()) {
	 bbOutput = unionFcn(predBasicBlockValues);
      } else {
	bbOutput = initBound;
      }
      mapBB2LiveOutVal[pBB] = bbOutput;
      
      
      DEBUG (dbgs() << "\n---------- Live variable at exit BB : "<< pBB->getName()  <<" Fcn: " << F.getName() << " ---------------\n");
      for (uint i = 0; i < bbOutput.size(); i++) {
	if (bbOutput[i]) {
	  DEBUG (dbgs() << "Live out: " << *idx2instMap[i]  << "\n");
	}
      }
      
      SmallVector<PHINode*, 4> phiNodeList;
      for (BasicBlock::reverse_iterator i = pBB->rbegin(), e = pBB->rend(); i != e; ++i) {
	Instruction *I = &*i;       
       
	if (isa<PHINode>(I)) {
	  phiNodeList.push_back(dyn_cast<PHINode>(I));
	} else {
	  std::vector<BitVector> instInfo = instGenAndKill(bbOutput, I, inst2idxMap);
	  bbOutput = livenessTrans(bbOutput, instInfo);
	}
      
      }
      
      if( !pBB->getSinglePredecessor() ) {
	DEBUG (dbgs() << "\n---------- Live variable at entry:" << pBB->getName() <<" Fcn: " << F.getName() << " ---------------\n");
	for (uint i = 0; i < bbOutput.size(); i++) {
	  if (bbOutput[i]) {
	    DEBUG (dbgs() << "Live in: " << *idx2instMap[i]  << "\n");
	  }
	}
      }
      
      // Process phi node
      for (pred_iterator PI = pred_begin(pBB); PI != pred_end(pBB); PI++){	 
	bbOutputTmp = bbOutput;
	for (auto phiIiter : phiNodeList) {
	  Instruction * phiI = dyn_cast<Instruction>(phiIiter);
	  // Kill the phi node
	  if( inst2idxMap.find(phiI) != inst2idxMap.end() ) {
	    int idx2kill = inst2idxMap[phiI];
	    bbOutputTmp.reset(idx2kill);
	  }   
	  
	  // Gen variable for this particular basic block
	  Instruction * incomingI = dyn_cast<Instruction>(phiIiter->getIncomingValueForBlock(*PI));
	  if( inst2idxMap.find(incomingI) != inst2idxMap.end() ) {
	    int idx2gen = inst2idxMap[incomingI];
	    bbOutputTmp.set(idx2gen);
	    DEBUG (dbgs() << "Gen variable ["<< to_string(idx2gen) << "]: " << *incomingI << "\n");
	  }
	  	  
	}
	bHaveChanged |= (mapBB2LiveInVal[pBB][*PI] != bbOutputTmp);
	mapBB2LiveInVal[pBB][*PI]  = bbOutputTmp;

	DEBUG (dbgs() << "\n---------- Live variable at entry:" << pBB->getName()  <<" to "<< (*PI)->getName()  <<" Fcn: " << F.getName() << " ---------------\n");
	for (uint i = 0; i < bbOutputTmp.size(); i++) {
	  if (bbOutputTmp[i]) {
	    DEBUG (dbgs() << "Live in: " << *idx2instMap[i]  << "\n");
	  }
	}
      }
    }
  }
  
  // Update LivenessInMap (live in)
  for (auto it = bbTraverse.rbegin() ; it != bbTraverse.rend() ; it++){
    BasicBlock* pBB = *it;
    for (pred_iterator PI = pred_begin(pBB); PI != pred_end(pBB); PI++) {
      BasicBlock * pred = *PI;
      BitVector value = mapBB2LiveInVal[pBB][pred];
      for (uint i = 0; i < value.size(); i++) {
	if (value[i]) {
	  LivenessInMap[pBB][pred].insert(idx2instMap[i]); 
	}
      }
    }    
  }

  // Update LivenessOutMap (live out)
  for (auto it = bbTraverse.rbegin() ; it != bbTraverse.rend() ; it++){
    BasicBlock* pBB = *it; 
    BitVector value = mapBB2LiveOutVal[pBB];
    for (uint i = 0; i < value.size(); i++) {
      if (value[i]) {
	LivenessOutMap[pBB].insert(idx2instMap[i]); 
      }
    }    
  }

  return;
}


LiveVariable::LivenessInMapTy &LiveVariable::getLiveInInstBBMap()  {
  return LivenessInMap;
}

LiveVariable::LivenessOutMapTy &LiveVariable::getLiveOutInstBBMap()  {
  return LivenessOutMap;
}

#if 0

char LiveVariableWrapperPass::ID = 0;

#if 1
INITIALIZE_PASS(LiveVariableWrapperPass, "livevariable", "Live Variable",
                      true, true)
#else

INITIALIZE_PASS_BEGIN(LiveVariableWrapperPass, "livevariable", "Live Variable",
                      true, true)
INITIALIZE_PASS_END(LiveVariableWrapperPass, "livevariable", "Live Variable",
                    true, true)

#endif

bool LiveVariableWrapperPass::runOnFunction(Function& F) {
  LV.recalculate(F);
  return false;
}

void LiveVariableWrapperPass::getAnalysisUsage(AnalysisUsage& AU) const {
  AU.setPreservesAll();
}

LiveVariable LiveVariableAnalysis::run(Function &F,
                                         FunctionAnalysisManager &) {
  LiveVariable LV;
  LV.recalculate(F);
  return LV;
}

AnalysisKey LiveVariableAnalysis::Key;

namespace llvm {

Pass *createLiveVariableWrapperPassPass() {
  return new LiveVariableWrapperPass();
}

}

#endif

//}
