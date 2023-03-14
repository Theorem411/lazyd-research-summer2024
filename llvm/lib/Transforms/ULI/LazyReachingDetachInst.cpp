#define DEBUG_TYPE "reaching-detach"

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InlineAsm.h"


#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"


#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Transforms/ULI/LazyReachingDetachInst.h"

using namespace llvm;

namespace {
  bool isReady(BitVector val) {
    return val.none();
  }
}

BitVector ReachingDetachInst::unionFcn (std::vector<BitVector> &values) {
  assert(values.size() > 0);
  BitVector res = values[0];
  for (std::vector<BitVector>::iterator value = values.begin(); value != values.end(); ++value) {
    res |= *value;
  }
  return res;
}


void ReachingDetachInst::runFlow(BasicBlock * entry, BitVector& initBound ) {
  bool bHaveChanged = true;
  while(bHaveChanged) {
    bHaveChanged = false;
    for(auto pBB : bbTraverse) {
      BitVector bbOutput;
      std::vector<BitVector> predBasicBlockValues;
      for( pred_iterator PI = pred_begin(pBB); PI != pred_end(pBB); PI++ ) {                
	BasicBlock* pred = *PI;
	
	// If one of the predecessor is a sync instruction, in is empty
	if(isa<SyncInst>(pred->getTerminator())) {
	  predBasicBlockValues.push_back(initBound);
	} else {
	  predBasicBlockValues.push_back(mapBB2OutVal[pred]);
	}
      }
      
      // If entry
      if(pBB == entry) {
	predBasicBlockValues.push_back(initBound);
      } 
      bbOutput = unionFcn(predBasicBlockValues);
      mapBB2InVal[pBB] = bbOutput;

      if( isa<DetachInst>(pBB->getTerminator()) ) {
	bbOutput.set(mapBB2idx[pBB]);
      }


      bHaveChanged |= (mapBB2OutVal[pBB] != bbOutput);
      mapBB2OutVal[pBB] = bbOutput;
    }
  }
}

void ReachingDetachInst::runFlowWithoutLoop( DominatorTree &DT, BasicBlock * entry, BitVector& initBound) {
  bool bHaveChanged = true;
  while(bHaveChanged) {
    bHaveChanged = false;
    for(auto pBB : bbTraverse) {
      BitVector bbOutput;
      std::vector<BitVector> predBasicBlockValues;
      for( pred_iterator PI = pred_begin(pBB); PI != pred_end(pBB); PI++ ) {                
	BasicBlock* pred = *PI;

	// Ignore self loop
	if (DT.dominates(pBB, pred) )
	    continue;

	// If one of the predecessor is a sync instruction, in is empty
	if(isa<SyncInst>(pred->getTerminator())) {
	  predBasicBlockValues.push_back(initBound);
	} else {
	  predBasicBlockValues.push_back(mapBB2OutValLoop[pred]);
	}

      }
      
      // If entry
      if(pBB == entry) {
	predBasicBlockValues.push_back(initBound);
      } 
      bbOutput = unionFcn(predBasicBlockValues);
      mapBB2InValLoop[pBB] = bbOutput;

      if( isa<DetachInst>(pBB->getTerminator()) ) {
	bbOutput.set(mapBB2idx[pBB]);
      }

      bHaveChanged |= (mapBB2OutValLoop[pBB] != bbOutput);
      mapBB2OutValLoop[pBB] = bbOutput;
    }
  }
}

void ReachingDetachInst::orderDetach(SmallVector<BasicBlock*, 4>& normalCfgBB, DenseMap<BasicBlock*, BitVector>& mapBB2Val, SmallVector<BasicBlock*, 4>& bbOrder, SmallVector<DetachInst*, 4>& bbOrderInst) {
  SmallVector<BasicBlock*, 4> bbList;  
  SmallVector<BasicBlock*, 4> bbTmp;  
  ValueMap<BasicBlock*, bool> haveVisited;  

  bbList.clear();
  do {
    if(!bbList.empty()) {
      // Inform the basic block that has dependency on it that it has been visited
      for(auto pBB : bbList) {
	unsigned pos = mapBB2idx[pBB];
	for (auto pBB2 : normalCfgBB) {	  
	  mapBB2Val[pBB2].reset(pos); 
	}	
      }
      bbList.clear();
    }
    for (auto pBB : normalCfgBB) {
      if(haveVisited.lookup(pBB)) 
	continue;
      
      BitVector val = mapBB2Val[pBB]; 
      if(isReady(val)) {
	bbTmp.push_back(pBB);    
	bbList.push_back(pBB);
	haveVisited[pBB] = true;
      }
    }
  } while (!bbList.empty());

  for(auto it = bbTmp.rbegin() ; it != bbTmp.rend(); it++ ) {
    auto pBB = *it;
    bbOrder.push_back(pBB);
    bbOrderInst.push_back(dyn_cast<DetachInst>(pBB->getTerminator()));
  }
  
}

void ReachingDetachInst::createOrderOfDetach( LoopInfo &LI, BitVector& initBB ) {
  // Create an order of detach starting from bottom to top  
  // Separate loop from normal control flow
  SmallVector<BasicBlock*, 4> normalCfgBB;
  SmallVector<BasicBlock*, 4> normalCfgOrderBB;
  SmallVector<BasicBlock*, 4> loopCfgBB;
  SmallVector<BasicBlock*, 4> bbList;
  SmallVector<BasicBlock*, 4> bbCurrentLoop;

  // Create a copy for temporary use
  DenseMap<BasicBlock*, BitVector> mapBB2InValCopy;
  DenseMap<BasicBlock*, BitVector> mapBB2InValLoopCopy;
  
  DenseMap<BasicBlock*, bool> haveVisited;
  DenseMap<BasicBlock*, bool> haveVisited2;  

  // Seperate detach based on whether it is in a loop or not
  for (auto di : detachList) {
    BasicBlock* parent = di->getParent();
    BitVector value = mapBB2InVal[parent]; 
    unsigned pos = mapBB2idx[parent];
    if (value[pos] == 1) {
      // It's a loop
      loopCfgBB.push_back(parent);
    } else {
      normalCfgBB.push_back(parent);
    }
    mapBB2InValCopy[parent]  = mapBB2InVal[parent];
    mapBB2InValLoopCopy[parent] = mapBB2InValLoop[parent];
    haveVisited[parent] = false;
  }
  
#if 1
  
  for (auto di : detachList) {
    BasicBlock* parent  =di->getParent();
    bbSeqOrder.push_back(parent);
    bbSeqOrderInst.push_back(di);
  }

#else
  // TODO: In matmul, when TRE enabled, one out of 4 detach instructions is not process
  // Process the sequential cfg 
  orderDetach(normalCfgBB, mapBB2InValCopy, bbSeqOrder, bbSeqOrderInst);
    
  DEBUG (dbgs() << " Order of Detach  \n");	
  for(auto pBB : bbSeqOrder) {   
    DEBUG (dbgs() << "Basicblock  : "<< pBB->getName() << "\n");	
  }

  auto loopOrder = LI.getLoopsInPreorder();
  for(auto it = loopOrder.rbegin(); it != loopOrder.rend() ; it++) {
    Loop * loops = *it;
    DEBUG (dbgs() << "Loops  : "<< loops->getName() << "\n");	    

    bbCurrentLoop.clear();
    for(auto pBB : loopCfgBB) {
      if(haveVisited.lookup(pBB)) {
	continue;
      }

      if(loops->contains(pBB)){
	haveVisited[pBB] = true;	
	bbCurrentLoop.push_back(pBB);
      }     
    }
    
    BitVector mask = initBB;
    for(auto pBB : bbCurrentLoop) {
      unsigned pos = mapBB2idx[pBB];
      mask.set(pos);
    }

    // Clear dependency outside the loop
    for(auto pBB : bbCurrentLoop) {
      BitVector val = mapBB2InValLoopCopy[pBB];
      val &= mask;
      mapBB2InValLoopCopy[pBB] = val;
    }

    //------------------------------------------------
    orderDetach(bbCurrentLoop, mapBB2InValLoopCopy, bbLoopOrder, bbLoopOrderInst);
    //------------------------------------------------
  }  
#endif

  DEBUG (dbgs() << " Order of loop  \n");	
  for( auto it = bbLoopOrder.begin(); it != bbLoopOrder.end() ; it++) {
    auto pBB  = *it;
    DEBUG (dbgs() << "Loop block  : "<< pBB->getName() << "\n");	
  }

}

// Return true if src can reach dst, otherwise false
bool ReachingDetachInst::isReaching(BasicBlock * src, BasicBlock * dst) {
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

unsigned ReachingDetachInst::createWorkList(BasicBlock * entry) {
  SmallVector<BasicBlock*, 4> bbList;
  ValueMap<BasicBlock*, bool> haveVisited;
  BasicBlock* bb = nullptr;
  unsigned idx = 0;

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
    mapBB2idx[bb] = idx;    
    idx++;
    
    // Check if it contains a detach inst
    if(isa<DetachInst>(bb->getTerminator())) {
      detachList.push_back(dyn_cast<DetachInst>(bb->getTerminator()));
    }

    // Check if it contains a sync inst
    if(isa<SyncInst>(bb->getTerminator())) {
      syncList.push_back(dyn_cast<SyncInst>(bb->getTerminator()));
    }

    for( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {                
      BasicBlock* succ = *SI;
      bbList.push_back(succ);
    }
  }

  return idx;
}

void ReachingDetachInst::recalculate(Function& F, FunctionAnalysisManager &AM, DominatorTree &DT, LoopInfo &LI) {
  // Get the entry of the basic block
  BasicBlock* entry = &F.getEntryBlock();  

  MapDetachToPath.clear();
  MapSyncToPath.clear();
  MapDetachToReachDetach.clear();
  bbTraverse.clear();
  mapBB2idx.clear();
  detachList.clear();
  syncList.clear();
  mapBB2InVal.clear();
  mapBB2OutVal.clear();
  mapBB2InValLoop.clear();
  mapBB2OutValLoop.clear();
  bbSeqOrder.clear();
  bbLoopOrder.clear();
  bbSeqOrderInst.clear();
  bbLoopOrderInst.clear();

  
  // Create the order of updating the basic block
  // while initializing a few data structure
  unsigned  idx = createWorkList(entry);

  // Initialize the entry 
  BitVector initBound = BitVector(idx, false);
  BitVector initBB = BitVector(idx, false);  
  for(auto pBB : bbTraverse) {
    mapBB2InVal[pBB] = initBB;
    mapBB2OutVal[pBB] = initBB;
    mapBB2InValLoop[pBB] = initBB;
    mapBB2OutValLoop[pBB] = initBB;
  }

  // Start performing the data flow analyze including loop if result is the same terminate
  //-------------------------------------------------------------------------
  runFlow(entry, initBound);
  // Start performing the data flow analyze excluding loop (removing backedge)
  //-------------------------------------------------------------------------
  runFlowWithoutLoop(DT, entry, initBound);
  
  // Can be optimize: performance of loop
  // Insert result into analysis
  for(auto di : detachList) {
    BasicBlock * parent = di->getParent();
    BitVector value = mapBB2InVal[parent]; 
    for (uint i = 0; i < value.size(); i++) {
      if (value[i]) {
	for (auto pBB : bbTraverse) {
	  BitVector v = mapBB2InVal[pBB];
	  // Basic block is in the path of detach with index i to the current detach (parent)
	  if(v[i] == 1 && isReaching(pBB, parent)) {
	    MapDetachToPath[di].insert(pBB);
	  }
	}	
      }
    }
  }

  for(auto si : syncList) {
    BasicBlock * parent = si->getParent();
    BitVector value = mapBB2InVal[parent]; 
    for (uint i = 0; i < value.size(); i++) {
      if (value[i]) {
	for (auto pBB : bbTraverse) {
	  BitVector v = mapBB2InVal[pBB];
	  // Basic block is in the path of detach with index i to the current detach (parent)
	  if(v[i] == 1 && isReaching(pBB, parent)) {
	    MapSyncToPath[si].insert(pBB);
	  }
	}	
      }
    }
  }

  
  // Traverse the BB and look if there is a reaching detach
  for(auto pBB : bbTraverse) {
    DEBUG (dbgs() << "================================\n");
    DEBUG (dbgs() << "Fcn: "<< F.getName() << " Basicblock : "<< pBB->getName() << "\n");
    BitVector value = mapBB2InVal[pBB]; 
    for (uint i = 0; i < value.size(); i++) {
      if (value[i]) {
	DEBUG (dbgs() << "Basicblock reaching to it : "<< bbTraverse[i]->getName() << "\n");	
      }
    }
  }
  
  // Find the reaching detach basic block
  for(auto di : detachList) {
    BasicBlock * parent = di->getParent();
    BitVector value = mapBB2InVal[parent]; 
    for (uint i = 0; i < value.size(); i++) {
      if (value[i]) {
	// Detach with index i reaches detach with basic block: parent
	MapDetachToReachDetach[di].insert(bbTraverse[i]);
      }
    }
  }
  
  createOrderOfDetach(LI, initBB);

  return;
}

ReachingDetachInst::MapDetachToBBTy  &ReachingDetachInst::getReachingDetachPathMap()  {
  return MapDetachToPath;
}

ReachingDetachInst::MapSyncToBBTy  &ReachingDetachInst::getReachingSyncPathMap()  {
  return MapSyncToPath;
}


ReachingDetachInst::MapDetachToBBTy  &ReachingDetachInst::getReachingDetachBBMap()  {
  return MapDetachToReachDetach;
}


SmallVector<BasicBlock*, 4>  &ReachingDetachInst::getSeqOrder()  {
  return bbSeqOrder;
}

SmallVector<BasicBlock*, 4>  &ReachingDetachInst::getLoopOrder()  {
  return bbLoopOrder;
}

SmallVector<DetachInst*, 4>  &ReachingDetachInst::getSeqOrderInst()  {
  return bbSeqOrderInst;
}

SmallVector<DetachInst*, 4>  &ReachingDetachInst::getLoopOrderInst()  {
  return bbLoopOrderInst;
}

DenseMap<BasicBlock*, BitVector> &ReachingDetachInst::getMapBB2InVal() {
  return mapBB2InVal;
}


#if 0

bool ReachingDetachInstWrapperPass::runOnFunction(Function& F) {
  FunctionAnalysisManager AM;

  auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

  RDI.recalculate(F, AM, DT, LI);
  return false;
}


void ReachingDetachInstWrapperPass::getAnalysisUsage(AnalysisUsage& AU) const {
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<DominatorTreeWrapperPass>();

  AU.addPreserved<LoopInfoWrapperPass>();
  AU.addPreserved<DominatorTreeWrapperPass>();
    
  //AU.setPreservesAll();
}

char ReachingDetachInstWrapperPass::ID = 0;


#if 1


INITIALIZE_PASS_BEGIN(ReachingDetachInstWrapperPass, "reachingdetachinst", "Reaching Detach Inst",
                      true, true)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(ReachingDetachInstWrapperPass, "reachingdetachinst", "Reaching Detach Inst",
                    true, true)

#else

RegisterPass<ReachingDetachInst> X("reaching-detach", "Reaching detach inst", /*Does not modify the CFG*/true, /*It's an analysis*/ true);

void initializeReachingDetachInstPass(PassRegistry&);

void ReachingDetachInst::registerClangPass(const PassManagerBuilder &, legacy::PassManagerBase &PM) {
  PM.add(new LoopInfoWrapperPass());
  PM.add(new DominatorTreeWrapperPass());
  PM.add(new ReachingDetachInst());
}

RegisterStandardPasses RegisterClangPass(PassManagerBuilder::EP_EarlyAsPossible, ReachingDetachInst::registerClangPass);

#endif

ReachingDetachInst ReachingDetachInstAnalysis::run(Function &F,
                                         FunctionAnalysisManager &AM) {
  ReachingDetachInst RDI;
  
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);

  RDI.recalculate(F, AM, DT, LI);
  return RDI;
}

AnalysisKey ReachingDetachInstAnalysis::Key;


namespace llvm {

Pass *createReachingDetachInstWrapperPassPass() {
  return new ReachingDetachInstWrapperPass();
}

}

#endif
