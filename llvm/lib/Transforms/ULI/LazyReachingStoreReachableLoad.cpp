#define DEBUG_TYPE "reaching-store-reachable-load"

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InlineAsm.h"


#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"


#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Transforms/ULI/LazyReachingStoreReachableLoad.h"

using namespace llvm;

namespace {
  bool isReady(BitVector val) {
    return val.none();
  }
}

// Return true if src can reach dst, otherwise false
bool ReachingStoreReachableLoad::isReaching(BasicBlock * src, BasicBlock * dst) {
  SmallVector<BasicBlock*, 4> bbList;
  ValueMap<BasicBlock*, bool> haveVisited;
  BasicBlock* bb = nullptr;

  // Src is destination itself, return true
  if(src == dst)
    return true;

  bbList.push_back(src);
  while(!bbList.empty()) {
    // Visit basic block
    bb = bbList.back();
    bbList.pop_back();
    
    // Basic block already visited, skip
    if(haveVisited.lookup(bb)){
      continue;
    }

    // Mark bb as visited
    haveVisited[bb] = true;    
    
    for( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {                
      BasicBlock* succ = *SI;
      // Find dst, return true
      if(succ == dst)
	return true;
      // Will Visit basic block that is a successor of the current basic block
      bbList.push_back(succ);
    }
  }

  // Did not found dst, return false
  return false;
}


BitVector ReachingStoreReachableLoad::unionFcnReachingAlloca (std::vector<BitVector> &values) {
  assert(values.size() > 0);
  BitVector res = values[0];
  for (std::vector<BitVector>::iterator value = values.begin(); value != values.end(); ++value) {
    res |= *value;
  }
  return res;
}

unsigned ReachingStoreReachableLoad::createWorkListReachingAlloca(BasicBlock * entry) {
  SmallVector<BasicBlock*, 4> bbList;
  ValueMap<BasicBlock*, bool> haveVisited;
  BasicBlock* bb = nullptr;
  unsigned idx = 0;
  
  // Traverse basic block and initialize store's pointer operand
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
    
    // Map store's pointer operand to idx and vice versa
    for (auto &ii: *bb) {
      if(isa<StoreInst>(&ii)) {
	StoreInst* si = dyn_cast<StoreInst> (&ii);	    
	Instruction* siPtr = dyn_cast<Instruction>(si->getPointerOperand());
	if(siPtr && !mapStr2IdxReachingAlloca.count(siPtr)) {
	  DEBUG (dbgs() << "Index i " << idx << "\n");
	  DEBUG (dbgs() << *siPtr << "\n");
	  mapStr2IdxReachingAlloca[siPtr] = idx;
	  mapIdx2StrReachingAlloca.push_back(siPtr);
	  idx++;
	}
      }
    } 

    // Create a map from basic block to idx
    for( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {                
      BasicBlock* succ = *SI;
      bbList.push_back(succ);
    }
  }

  return idx;
}

void ReachingStoreReachableLoad::runFlowReachingAlloca(BasicBlock * entry, BitVector& initBoundReachingAlloca ) {
  bool bHaveChanged = true;
  while(bHaveChanged) {
    bHaveChanged = false;
    for(auto pBB : bbTraverse) {
      BitVector bbOutput;
      std::vector<BitVector> predBasicBlockValues;
      for( pred_iterator PI = pred_begin(pBB); PI != pred_end(pBB); PI++ ) {                
	BasicBlock* pred = *PI;
	predBasicBlockValues.push_back(mapBB2OutValReachingAlloca[pred]);
      }
      
      // If entry
      if(pBB == entry) {
	predBasicBlockValues.push_back(initBoundReachingAlloca);
      }
      
      bbOutput = unionFcnReachingAlloca(predBasicBlockValues);
      mapBB2InValReachingAlloca[pBB] = bbOutput;
      
      // Set if store's pointer operand is found
      for (auto &ii: *pBB) {
	if(isa<StoreInst>(&ii)) {
	  StoreInst* si = dyn_cast<StoreInst> (&ii);	    
	  Instruction* siPtr = dyn_cast<Instruction>(si->getPointerOperand());
	  bbOutput.set(mapStr2IdxReachingAlloca[siPtr]);
	}
      }
      
      bHaveChanged |= (mapBB2OutValReachingAlloca[pBB] != bbOutput);
      mapBB2OutValReachingAlloca[pBB] = bbOutput;
    }
  }
}


std::vector<BitVector> ReachingStoreReachableLoad::unionFcnReachingStore (std::vector<std::vector<BitVector>> &values, unsigned nStrPtr) {
  assert(values.size() > 0);
  std::vector<BitVector> resVec;

  // Initialization
  for(unsigned i=0; i< nStrPtr; i++) {
    resVec.push_back(values[0][i]);
  }

  for (std::vector<std::vector<BitVector>>::iterator value = values.begin(); value != values.end(); ++value) {  
    for(unsigned i=0; i< nStrPtr; i++) {
      resVec[i] |=  (*value)[i];
    }    
  }
  return resVec;
}

SmallVector<unsigned, 4> ReachingStoreReachableLoad::createWorkListReachingStore(BasicBlock * entry, unsigned nStrPtr) {
  SmallVector<BasicBlock*, 4> bbList;
  ValueMap<BasicBlock*, bool> haveVisited;
  BasicBlock* bb = nullptr;
  SmallVector<unsigned, 4> idxVal;
  
  for(unsigned i=0; i< nStrPtr; i++) {
    idxVal.push_back(0); 
  }
  
  // Traverse basic block and initialize store's pointer operand
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
    
    // Map store's pointer operand to idx and vice versa
    for (auto &ii: *bb) {
      if(isa<StoreInst>(&ii)) {
	StoreInst* si = dyn_cast<StoreInst> (&ii);	    
	Instruction* siPtr = dyn_cast<Instruction>(si->getPointerOperand());
	unsigned entryIdx = mapStr2IdxReachingAlloca[siPtr];

	if(siPtr && !mapVal2IdxReachingStore[siPtr].count(si)) {	
	  mapVal2IdxReachingStore[siPtr][si] = idxVal[entryIdx];
	  idxVal[entryIdx]++;
	  mapIdx2ValReachingStore[siPtr].push_back(si);

	}
      }
    } 

    // Create a map from basic block to idx
    for( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {                
      BasicBlock* succ = *SI;
      bbList.push_back(succ);
    }
  }
  return idxVal;
}


void ReachingStoreReachableLoad::runFlowReachingStore(BasicBlock * entry, SmallVector<unsigned, 4>& idxVal ) {
  bool bHaveChanged = true;
  unsigned nAlloca = idxVal.size();

  while(bHaveChanged) {
    bHaveChanged = false;
    for(auto pBB : bbTraverse) {
      std::vector<BitVector> bbOutput;
      std::vector< std::vector<BitVector> > predBasicBlockValues;
      for( pred_iterator PI = pred_begin(pBB); PI != pred_end(pBB); PI++ ) {                
	BasicBlock* pred = *PI;
	predBasicBlockValues.push_back(mapBB2OutValReachingStore[pred]);
      }
      
      // If entry
      if(pBB == entry) {
	std::vector<BitVector> tmpVal;
	for(unsigned i=0; i< nAlloca; i++) {
	  tmpVal.push_back((BitVector(idxVal[i], false)));
	}
	predBasicBlockValues.push_back((tmpVal));
      }
      
      bbOutput = (unionFcnReachingStore(predBasicBlockValues, nAlloca));
      

      for(unsigned i=0; i< nAlloca; i++) {
	mapBB2InValReachingStore[pBB][i] = bbOutput[i];
      }

      // Set if store instruction operand and kill the previous one
      for (auto &ii: *pBB) {
	if(isa<StoreInst>(&ii)) {
	  StoreInst* si = dyn_cast<StoreInst> (&ii);	    
	  Instruction* siPtr = dyn_cast<Instruction>(si->getPointerOperand());
	  unsigned entryIdx = mapStr2IdxReachingAlloca[siPtr];

	  // Reset previous result
	  bbOutput[entryIdx].reset();
	  
	  // Set new result
	  bbOutput[entryIdx].set(mapVal2IdxReachingStore[siPtr][si]);
	}
      }
      
      for(unsigned i=0; i< nAlloca; i++) {
	bHaveChanged |= (mapBB2OutValReachingStore[pBB][i] != bbOutput[i]);
	mapBB2OutValReachingStore[pBB][i] = bbOutput[i];      
      }

    }
  }
}

void ReachingStoreReachableLoad::recalculate(Function& F, FunctionAnalysisManager &AM, DominatorTree &DT, LoopInfo &LI) {
  // Get the entry of the basic block
  BasicBlock* entry = &F.getEntryBlock();
  DEBUG(dbgs() << "ReachingStoreReachableLoad : " << F.getName() << "\n");
  // Clear
  bbTraverse.clear();
  mapStr2IdxReachingAlloca.clear();
  mapIdx2StrReachingAlloca.clear();  
  mapBB2InValReachingAlloca.clear();
  mapBB2OutValReachingAlloca.clear();  
  MapBB2ReachingAlloca.clear();

  // TODO: Maybe removed, not needed
#if 0
  // Clear
  for (auto elem : mapVal2IdxReachingStore) {
    elem->second.clear();
  }
  mapVal2IdxReachingStore.clear();
  for (auto elem : mapIdx2ValReachingStore) {
    elem->second.clear();
  }
  mapIdx2ValReachingStore.clear();
  for(auto elem : mapBB2InValReachingStore) {
    elem->second.clear();
  }
  mapBB2InValReachingStore.clear();
  for(auto elem : mapBB2OutValReachingStore) {
    elem->second.clear();
  }
  mapBB2OutValReachingStore.clear();
#endif  

  // ----------------------------------------------------------------------------------------------------
  // First Flow, reaching alloca
  // Create the order of updating the basic block
  // while initializing a few data structure
  unsigned  idx = createWorkListReachingAlloca(entry);
  
  if(!idx)
    return;

  // Initialize the entry 
  BitVector initBoundReachingAlloca = BitVector(idx, false);
  BitVector initBBReachingAlloca = BitVector(idx, false);  
  for(auto pBB : bbTraverse) {
    mapBB2InValReachingAlloca[pBB] = initBBReachingAlloca;
    mapBB2OutValReachingAlloca[pBB] = initBBReachingAlloca;
  }

  // First flow, reaching alloca that contain store
  runFlowReachingAlloca(entry, initBoundReachingAlloca);
  
  // For each basic block, get the reaching store's pointer operand
  for (auto &bb : F) {
    auto value =  mapBB2OutValReachingAlloca[&bb];
    DEBUG (dbgs() << "BB: " << bb.getName() <<" Reaching Pointer:\n");
    for (uint i = 0; i < value.size(); i++) {
      if (value[i]) {
	MapBB2ReachingAlloca[&bb].insert(mapIdx2StrReachingAlloca[i]);	
	DEBUG (dbgs() << "Index: "  << i << "\n"); 
	DEBUG (dbgs() << *mapIdx2StrReachingAlloca[i] << "\n");
      }
    }
  }  
  // ----------------------------------------------------------------------------------------------------  
  // TODO: Not used in the end, may be removed
#if 0
  // Clear bbTraverse
  bbTraverse.clear();
  auto idxVal = (createWorkListReachingStore(entry, idx));
  
  for(auto pBB : bbTraverse) {
    for(unsigned i=0; i< idx; i++) {
      mapBB2InValReachingStore[pBB].push_back(BitVector(idxVal[i], false));
      mapBB2OutValReachingStore[pBB].push_back(BitVector(idxVal[i], false));
    }  
  }

  // Second Flow, reaching store
  runFlowReachingStore(entry, idxVal);
  
  // Test if it is working
  for (auto &bb : F) {
    auto values =  mapBB2OutValReachingStore[&bb];      
    for (uint i = 0; i < values.size(); i++) {
      auto value = values[i];
      auto siPtr = mapIdx2StrReachingAlloca[i];      
      for (uint j = 0; j < value.size(); j++) {
	if (value[j]) {
	  auto strinst = mapIdx2ValReachingStore[siPtr][j];
	  //MapBB2ReachingAlloca[&bb].insert(mapIdx2StrReachingAlloca[i]);		
	}
      }
    }
  }  
#endif  

  return;
}

#if 0

bool ReachingStoreReachableLoadWrapperPass::runOnFunction(Function& F) {
  FunctionAnalysisManager AM;

  auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

  RSI.recalculate(F, AM, DT, LI);
  return false;
}


void ReachingStoreReachableLoadWrapperPass::getAnalysisUsage(AnalysisUsage& AU) const {
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<DominatorTreeWrapperPass>();
  
  AU.addPreserved<LoopInfoWrapperPass>();
  AU.addPreserved<DominatorTreeWrapperPass>();
  
  //AU.setPreservesAll();
}

char ReachingStoreReachableLoadWrapperPass::ID = 0;

#if 1


INITIALIZE_PASS_BEGIN(ReachingStoreReachableLoadWrapperPass, "reachingstorereachableload", "Reaching Store reachable load",
                      true, true)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(ReachingStoreReachableLoadWrapperPass, "reachingstorereachableload", "Reaching Store reachable load",
                    true, true)


#else

RegisterPass<ReachingStoreReachableLoad> X("reaching-store-reachable-load", "Reaching store inst and reachable load", /*Does not modify the CFG*/true, /*It's an analysis*/ true);

void initializeReachingStoreReachableLoadInstPass(PassRegistry&);

void ReachingStoreReachableLoad::registerClangPass(const PassManagerBuilder &, legacy::PassManagerBase &PM) {
  PM.add(new LoopInfoWrapperPass());
  PM.add(new DominatorTreeWrapperPass());
  PM.add(new ReachingStoreReachableLoad());
}

RegisterStandardPasses RegisterClangPass(PassManagerBuilder::EP_EarlyAsPossible, ReachingStoreReachableLoad::registerClangPass);

#endif

ReachingStoreReachableLoad ReachingStoreReachableLoadAnalysis::run(Function &F,
                                         FunctionAnalysisManager &AM) {
  ReachingStoreReachableLoad RSI;
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);

  RSI.recalculate(F, AM, DT, LI);
  return RSI;
}

AnalysisKey ReachingStoreReachableLoadAnalysis::Key;

namespace llvm {

Pass *createReachingStoreReachableLoadWrapperPassPass() {
  return new ReachingStoreReachableLoadWrapperPass();
}

}
#endif
