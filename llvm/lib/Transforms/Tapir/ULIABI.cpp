//===- ULIABI.cpp - Lower Tapir into ULI PRSC runtime system calls -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the ULI ABI to convert Tapir instructions to calls
// into the user-level-interrupts PRSC library.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Tapir/ULIABI.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/Tapir/Outline.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/EscapeEnumerator.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/TapirUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

//TODO : Generate suspend routine


using namespace llvm;

#define DEBUG_TYPE "uliabi"

#define MAX_LEVEL 4

StoreInst  * storeInstArr[MAX_LEVEL];
BasicBlock * genWorkBB[MAX_LEVEL];
BasicBlock * seedGeneration;
BasicBlock * lastFalseBB;
BasicBlock * firstDetach;
BasicBlock * lastDetach;
BasicBlock * syncResumeBB;
Value * prscDescLocal;
Value * pRA;
Value * seedLocal;

SmallVector<BasicBlock *, 8> CounterZeroBBVec;

DenseMap<Function *, Function *> WrapperMap;
DenseMap<Function *, Function *> WorkReplyHandlerMap;
DenseMap<Function *, BasicBlock *> SyncBBMap;
using Sync = ULIABI::Sync;
using Work = ULIABI::Work;
using PRSC_Desc = ULIABI::PRSC_Desc;
using Seed = ULIABI::Seed;
unsigned detachLevel = 0;

/// Helper methods for storing to and loading from struct fields.
static Value *GEP(IRBuilder<> &B, Value *Base, int field) {
  // return B.CreateStructGEP(cast<PointerType>(Base->getType()),
  //                          Base, field);
  return B.CreateConstInBoundsGEP2_32(nullptr, Base, 0, field);
}

static unsigned GetAlignment(const DataLayout &DL, StructType *STy, int field) {
  return DL.getPrefTypeAlignment(STy->getElementType(field));
}

static void StoreSTyField(IRBuilder<> &B, const DataLayout &DL, StructType *STy,
                          Value *Val, Value *Dst, int field,
                          bool isVolatile = false,
                          AtomicOrdering Ordering = AtomicOrdering::NotAtomic) {
  StoreInst *S = B.CreateAlignedStore(Val, GEP(B, Dst, field),
                                      GetAlignment(DL, STy, field), isVolatile);
  S->setOrdering(Ordering);
}

static Value *LoadSTyField(
    IRBuilder<> &B, const DataLayout &DL, StructType *STy, Value *Src,
    int field, bool isVolatile = false,
    AtomicOrdering Ordering = AtomicOrdering::NotAtomic) {
    LoadInst *L =  B.CreateAlignedLoad(GEP(B, Src, field),
                                     GetAlignment(DL, STy, field), isVolatile);
  L->setOrdering(Ordering);
  return L;
}

using TypeBuilderCache = std::map<LLVMContext *, StructType *>;


#define DEFAULT_GET_LIB_FUNC(name)                          \
  static Constant *Get_##name(Module& M) {                  \
    return M.getOrInsertFunction( #name,                    \
        TypeBuilder< name##_ty, false>::get(M.getContext()) \
      );                                                    \
  }

using ENAULI_ty = void (unsigned long);
DEFAULT_GET_LIB_FUNC(ENAULI)

using PRSC_DEC_JOIN_ty = void (Sync*);
DEFAULT_GET_LIB_FUNC(PRSC_DEC_JOIN)

using PRSC_CHECKIFZERO_RESUME_ty = int (Sync*);
DEFAULT_GET_LIB_FUNC(PRSC_CHECKIFZERO_RESUME)

using PRSC_RESET_WORKSTEAL_ty = void (void);
DEFAULT_GET_LIB_FUNC(PRSC_RESET_WORKSTEAL)

using PRSC_POPFRONT_SEEDQ_ty = void (void);
DEFAULT_GET_LIB_FUNC(PRSC_POPFRONT_SEEDQ)

using PRSC_PUSHFRONT_SEEDQ_ty = void (Seed*);
DEFAULT_GET_LIB_FUNC(PRSC_PUSHFRONT_SEEDQ)

using PRSC_SET_JOIN_ty = void (Sync*, int);
DEFAULT_GET_LIB_FUNC(PRSC_SET_JOIN)

using PRSC_SUSPEND_ROUTINE_ty = void (void);
DEFAULT_GET_LIB_FUNC(PRSC_SUSPEND_ROUTINE)

using PRSC_RESUME_TO_HANDLER_ty = void (int );
DEFAULT_GET_LIB_FUNC(PRSC_RESUME_TO_HANDLER)

using PRSC_PUSHFRONT_WORKQ_ty = void (Work*);
DEFAULT_GET_LIB_FUNC(PRSC_PUSHFRONT_WORKQ)

// Argument too much?, cause compilation error
//using PRSC_CREATE_WORK_ty = Work*(void*,int,int,void*,void*,Sync*,void*,int);
//DEFAULT_GET_LIB_FUNC(PRSC_CREATE_WORK)

typedef void* (*FP)(void);
using Scalar = long long int;
using UliArgType = long long int;


// typedef struct {
//     char bEnqResume;
//     uint counter;
//     char seedStolen;
// } Sync;

namespace llvm {
template <bool X>
class TypeBuilder<Sync, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    // Try looking up this type by name.
    StructType *ExistingTy = StructType::lookupOrCreate(C, "Sync");
    cache[&C] = ExistingTy;
    StructType *NewTy = StructType::create(C);
    NewTy->setBody(
        TypeBuilder<char, X>::get(C), // bEnqResume
        TypeBuilder<uint, X>::get(C), // counter
        TypeBuilder<char, X>::get(C)  // seedStolen
                          );
    if (ExistingTy->isOpaque())
      ExistingTy->setBody(NewTy->elements());
    else {
      assert(ExistingTy->isLayoutIdentical(NewTy) &&
             "Conflicting definition of type struct.Sync");
    }
    return ExistingTy;
  }
  enum {
    bEnqResume,
    counter,
    seedStolen
  };
};
}

using SyncType = TypeBuilder<Sync, false>;

// struct Work {
//     FP fp;
//     int id;
//     Scalar* argv;
//     uint argc;
//     Scalar* res;
//     Sync* pSync;
//     Work* next;
//     Work* prev;
//     int stolen;
//     int realized;
//     unsigned int src;
// };

namespace llvm {
template <bool X>
class TypeBuilder<Work, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    // Try looking up this type by name.
    StructType *ExistingTy = StructType::lookupOrCreate(C, "Work");
    cache[&C] = ExistingTy;
    StructType *NewTy = StructType::create(C);
    NewTy->setBody(
        TypeBuilder<FP, X>::get(C), // fp
        TypeBuilder<int, X>::get(C), // id
        TypeBuilder<Scalar*, X>::get(C), // argv
        TypeBuilder<uint, X>::get(C), // argc
        TypeBuilder<Scalar*, X>::get(C), // res
        TypeBuilder<Sync*, X>::get(C), // pSync
        TypeBuilder<Work*, X>::get(C), // next
        TypeBuilder<Work*, X>::get(C), // prev
        TypeBuilder<int, X>::get(C), // stolen
        TypeBuilder<int, X>::get(C), // realized
        TypeBuilder<unsigned int, X>::get(C)  // src
                          );
    if (ExistingTy->isOpaque())
      ExistingTy->setBody(NewTy->elements());
    else {
      assert(ExistingTy->isLayoutIdentical(NewTy) &&
             "Conflicting definition of type struct.Work");
    }
    return ExistingTy;
  }
  enum {
    fp,
    id,
    argv,
    argc,
    res,
    pSync,
    next,
    prev,
    stolen,
    realized,
    src
  };
};
}
using WorkType = TypeBuilder<Work, false>;

// typedef struct {
//
//
//
// } PRSC_Desc

namespace llvm{
template <bool X>
class TypeBuilder<PRSC_Desc, X> {
public:
  static StructType *get(LLVMContext &C){
      static TypeBuilderCache cache;
      TypeBuilderCache::iterator I = cache.find(&C);
      if(I != cache.end())
          return I->second;
      StructType *ExistingTy = StructType::lookupOrCreate(C, "PRSC_Desc");
      cache[&C] = ExistingTy;
      StructType *NewTy = StructType::create(C);
      NewTy->setBody(
                     TypeBuilder<Sync, X>::get(C), // Sync
                     TypeBuilder<char, X>::get(C), // bpushback
                     TypeBuilder<Scalar*, X>::get(C),  // res
                     TypeBuilder<Work*, X>::get(C), // work
                     TypeBuilder<void*, X>::get(C), // bp
                     TypeBuilder<void*, X>::get(C),  // sp
                     TypeBuilder<void*, X>::get(C), // resumeip
                     TypeBuilder<void*, X>::get(C),  // handlerip
                     TypeBuilder<void*, X>::get(C), // handlersp
                     TypeBuilder<void*, X>::get(C)  // handlerbp
      
                     );
      if(ExistingTy->isOpaque())
          ExistingTy->setBody(NewTy->elements());
      else
          assert(ExistingTy->isLayoutIdentical(NewTy) && 
                 "Conflicting definition of type struct.PRSC_Desc");

      return ExistingTy;
  }
  enum {
      sync,
      bpushback,
      res, 
      work,
      bp,
      sp,
      resumeip,      
      handlerip,
      handlersp,
      handlerbp
  };
};
}

using PRSC_DescType = TypeBuilder<PRSC_Desc, false>;

namespace llvm{
template <bool X>
class TypeBuilder<Seed, X> {
public:
  static StructType *get(LLVMContext &C){
      static TypeBuilderCache cache;
      TypeBuilderCache::iterator I = cache.find(&C);
      if(I != cache.end())
          return I->second;
      StructType *ExistingTy = StructType::lookupOrCreate(C, "Seed");
      cache[&C] = ExistingTy;
      StructType *NewTy = StructType::create(C);
      NewTy->setBody(
                     TypeBuilder<void*, X>::get(C),  // sp
                     TypeBuilder<void*, X>::get(C)  // ip                           
                     );
      if(ExistingTy->isOpaque())
          ExistingTy->setBody(NewTy->elements());
      else
          assert(ExistingTy->isLayoutIdentical(NewTy) && 
                 "Conflicting definition of type struct.PRSC_Desc");

      return ExistingTy;
  }
  enum {
      sp,
      ip
  };
};
}

using SeedType = TypeBuilder<Seed, false>;

/*
/// \brief Helper to find a function with the given name, creating it if it
/// doesn't already exist. If the function needed to be created then return
/// false, signifying that the caller needs to add the function body.
template <typename T>
static bool GetOrCreateFunction(const char *FnName, Module& M,
                                Function *&Fn,
                                Function::LinkageTypes Linkage =
                                Function::InternalLinkage,
                                bool DoesNotThrow = true) {
  LLVMContext &Ctx = M.getContext();

  Fn = M.getFunction(FnName);

  // if the function already exists then let the
  // caller know that it is complete
  if (Fn)
    return true;

  // Otherwise we have to create it
  FunctionType *FTy = TypeBuilder<T, false>::get(Ctx);
  Fn = Function::Create(FTy, Linkage, FnName, &M);

  // Set nounwind if it does not throw.
  if (DoesNotThrow)
    Fn->setDoesNotThrow();

  // and let the caller know that the function is incomplete
  // and the body still needs to be added
  return false;
}
*/

Value *ULIABI::lowerGrainsizeCall(CallInst *GrainsizeCall) {
  assert(false);
  return nullptr;
}

void ULIABI::createSync(SyncInst &SI, ValueToValueMapTy &DetachCtxToStackFrame) {
    IRBuilder<> B(lastFalseBB);
    B.CreateUnreachable();
    
    BasicBlock &BB = *(SI.getParent());
    Function &Fn = *(BB.getParent());
    Module &M = *(Fn.getParent());

    BasicBlock * syncBB = SI.getSuccessor(0);
    // TODO :  sync?sync_region should be the key instead of function since one function can have multiple sync statement 
    SyncBBMap[&Fn] = syncBB;

    //assert(false);

}

Function *ULIABI::createDetach(DetachInst &Detach,
                        ValueToValueMapTy &DetachCtxToStackFrame,
                        DominatorTree &DT, AssumptionCache &AC) {

    BasicBlock * curBB = Detach.getParent();
    Function * F = curBB->getParent();
    Module * M = F->getParent();
    LLVMContext& C = M->getContext();
    BasicBlock * detachBlock = Detach.getDetached();    
    BasicBlock *Continue = Detach.getContinue();
    const DataLayout &DL = M->getDataLayout();
    
    
    // Create the work Generation
    SmallVector<BasicBlock*, 8> bbV2Clone;
    SmallVector<BasicBlock*, 8> bbList;
    DenseMap<BasicBlock *, bool> haveVisited;
    ValueToValueMapTy VMap;    
    BasicBlock * bb = nullptr;
    Instruction * term = nullptr;
    bool bIgnore = false;
    
    SmallVector<Instruction *,2> del_instrs;
  
    Type *VoidPtrTy = TypeBuilder<void*, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);
    Value *Zero = ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
    //Instruction * storeInstAfterCall = nullptr;


    // Look for potential Store operation
    StoreInst * potentialSt = dyn_cast<StoreInst>(detachBlock->getFirstNonPHIOrDbgOrLifetime()->getNextNode() );
    if(potentialSt){                    
        // Get the IR to store
        Value *arg0 = potentialSt->getOperand(0);
        arg0->dump();

        Instruction * callInst = detachBlock->getFirstNonPHIOrDbgOrLifetime();
        callInst->dump();
        // Check if it is the same with the call instruction
        if( !arg0->getName().compare(callInst->getName()) ){
            storeInstArr[detachLevel] = dyn_cast<StoreInst>( potentialSt->clone() );                        
            storeInstArr[detachLevel]->setName(potentialSt->getName());
        } 
                   

    }
    
    if(detachLevel==0){
        lastDetach = detachBlock;
    }
    firstDetach =   curBB;
    // Search 
    bbList.push_back(Continue);
    while(!bbList.empty()){
        bb = bbList.back();
        bbList.pop_back();
        if ( (haveVisited.lookup(bb)) ){
            continue;
        }
        haveVisited[bb] = true;

        if ( (term = dyn_cast<DetachInst>(bb->getTerminator())) ){
            bbV2Clone.push_back(bb);
            bb = dyn_cast<DetachInst>(term)->getDetached();
            bbList.push_back(bb);
        } else if ( (term = dyn_cast<ReattachInst>(bb->getTerminator()))  ){
            bbV2Clone.push_back(bb);
        } else if ( (term = dyn_cast<SyncInst>(bb->getTerminator())) ){
            bbV2Clone.push_back(bb);
        } else {
            bbV2Clone.push_back(bb);
            for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
                bbList.push_back(*SI);
            }
        }
    }
  

    
    // Work generation for thief
    if(!bIgnore){
        for(auto BB : bbV2Clone){
            BasicBlock *bbC = CloneBasicBlock(BB, VMap, ".workGen_Steal", F, nullptr,
                                      nullptr);
            VMap[BB] = bbC;            
        }

        genWorkBB[detachLevel] = dyn_cast<BasicBlock>(VMap[Continue]);
        errs() << "Gen work : "<<  detachLevel << " \n";        
        genWorkBB[detachLevel]->dump();

        //TODO : Fix up the instruction(argument etc) and refactoring
        Instruction * potentialCall = nullptr;
        bool bFoundPotentialCall = false;
        for(auto BB : bbV2Clone){

            BasicBlock *CBB = dyn_cast<BasicBlock>(VMap[BB]);
            Instruction *iterm  = CBB->getTerminator();
            if(DetachInst * itermDet = dyn_cast<DetachInst>(iterm)){
                BasicBlock * detachBlock = itermDet->getDetached();
                BranchInst *detachBr = BranchInst::Create(detachBlock);
                ReplaceInstWithInst(itermDet, detachBr);

 
            } else if(ReattachInst * itermRet = dyn_cast<ReattachInst>(iterm)){                
                Instruction * instr = CBB->getFirstNonPHIOrDbgOrLifetime();
                CallInst * callInst = dyn_cast<CallInst>(instr);
                CallInst * callInstOri = dyn_cast<CallInst>(BB->getFirstNonPHIOrDbgOrLifetime());
                assert(callInst && "First instruction not a call instruction. Seems like something is wrong");

                SmallVector<Value*, 8> Args;
                for (int i = 0; i<callInst->getNumOperands()-1; i++){
                    //    Args.push_back(callInst->getOperand(i));
                    //callInst->getOperand(i)->dump();
                }
                
                IRBuilder<> B(instr);

                Type *VoidPtrTy = TypeBuilder<void*, false>::get(C);
                Type *PRSC_DescTy = TypeBuilder<PRSC_Desc*, false>::get(C);
                Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);

                Value *WrapperPtr = B.CreateBitCast(WrapperMap.lookup(F), VoidPtrTy);
                Value *WorkReplyHandlerPtr = B.CreateBitCast(WorkReplyHandlerMap.lookup(F), VoidPtrTy);

                Args.push_back(WorkReplyHandlerPtr); // Handler
                Args.push_back(WrapperPtr); // Function wrapper
                // Functions argument
                for (User::op_iterator it = callInst->arg_begin(); it != callInst->arg_end(); it++){
                    Args.push_back(it->get());
                }
                // Basic Block to resume after all child have return
                BlockAddress* bA = BlockAddress::get(syncResumeBB);
                Args.push_back(bA);
                // SP
                Value * pSeedSP  = B.CreateStructGEP(SeedType::get(C), seedLocal, (unsigned)SeedType::sp);    
                Value * seedSP = B.CreateLoad(IntegerType::getInt8Ty(C)->getPointerTo(), pSeedSP);
                Args.push_back(seedSP);
                // Sync
                Value * PRSCSync  = B.CreateStructGEP(PRSC_DescType::get(C), prscDescLocal, (unsigned)PRSC_DescType::sync);    
                Args.push_back(PRSCSync);
                // Variable to store the result
                if(storeInstArr[detachLevel]){
                    Args.push_back(storeInstArr[detachLevel]->getPointerOperand());
                } else {
                    Args.push_back(ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo()));
                }
        
                Function *UliReply = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_reply);
                B.CreateCall(UliReply, Args);

                Value *Zero = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
                Constant *PRSC_RESUME_TO_HANDLER = Get_PRSC_RESUME_TO_HANDLER(*M);
                B.CreateCall(PRSC_RESUME_TO_HANDLER, Zero);
                                
                B.CreateUnreachable();
                
                del_instrs.push_back(instr->getNextNode());
                del_instrs.push_back(instr);
                del_instrs.push_back(iterm);

                
            } else {
                for(Instruction &I : *CBB){
                    if(CallInst * callInst = dyn_cast<CallInst>(&I)){
                        //genWorkBB[detachLevel] = CBB;
                        DEBUG(dbgs() << "Instruction to send\n");                            
                        potentialCall = &I;
                        bFoundPotentialCall = true;
                    }
                }
            }

            if ( SyncInst * itermSync = dyn_cast<SyncInst>(iterm) ) {
                if(bFoundPotentialCall){
                    CallInst * callInst = dyn_cast<CallInst>(potentialCall);
                    IRBuilder<> B(potentialCall);
                    SmallVector<Value*, 8> Args;
                    
                    Type *VoidPtrTy = TypeBuilder<void*, false>::get(C);
                    Type *PRSC_DescTy = TypeBuilder<PRSC_Desc*, false>::get(C);
                    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);
                    Value *Zero = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
                    

                    Value *WrapperPtr = B.CreateBitCast(WrapperMap.lookup(F), VoidPtrTy);
                    Value *WorkReplyHandlerPtr = B.CreateBitCast(WorkReplyHandlerMap.lookup(F), VoidPtrTy);

                    Args.push_back(WorkReplyHandlerPtr); // Handler
                    Args.push_back(WrapperPtr); // Function wrapper
                    // Functions argument
                    for (User::op_iterator it = callInst->arg_begin(); it != callInst->arg_end(); it++){
                        Args.push_back(it->get());
                    }
                    // Basic Block to resume after all child have return
                    BlockAddress* bA = BlockAddress::get(syncResumeBB);
                    Args.push_back(bA);
                    // SP
                    Value * pSeedSP  = B.CreateStructGEP(SeedType::get(C), seedLocal, (unsigned)SeedType::sp);    
                    Value * seedSP = B.CreateLoad(IntegerType::getInt8Ty(C)->getPointerTo(), pSeedSP);
                    Args.push_back(seedSP);
                    // Sync
                    Value * PRSCSync  = B.CreateStructGEP(PRSC_DescType::get(C), prscDescLocal, (unsigned)PRSC_DescType::sync);    
                    Args.push_back(PRSCSync);
                    // Variable to store the result
                    if(storeInstArr[detachLevel]){
                        Args.push_back(storeInstArr[detachLevel]->getPointerOperand());
                    } else {
                        Args.push_back(ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo()));
                    }
        
                    Function *UliReply = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_reply);
                    B.CreateCall(UliReply, Args);            
    
                    Constant *PRSC_RESUME_TO_HANDLER = Get_PRSC_RESUME_TO_HANDLER(*M);
                    B.CreateCall(PRSC_RESUME_TO_HANDLER, ConstantInt::get(Int32Ty, 2, /*isSigned=*/false));
                    B.CreateUnreachable();
                    
                    del_instrs.push_back(potentialCall->getNextNode());
                    del_instrs.push_back(potentialCall);
                    del_instrs.push_back(iterm);
                }
            }
              
            // Remap instruction
            for (Instruction &II : *CBB) {
                RemapInstruction(&II, VMap,
                                 RF_IgnoreMissingLocals,
                                 nullptr, nullptr);
            }
            
                        
        }
        

    }


    for (auto In : del_instrs){
        Instruction& inst = *In;
        inst.eraseFromParent(); // delete instrs
    }

    // TODO :
    // Got stolen case
    BasicBlock * gotStolenArr[MAX_LEVEL];
    gotStolenArr[0] = BasicBlock::Create(C, "gotStolen", F);
    IRBuilder<> gotStolenB (gotStolenArr[0]);
    int tmpLevel = detachLevel;
    
    // Store result of function
    if(storeInstArr[detachLevel]){
        gotStolenB.Insert(storeInstArr[detachLevel], storeInstArr[detachLevel]->getName());
    }
    // Decrement counter
    Value * PRSCSync  = gotStolenB.CreateStructGEP(PRSC_DescType::get(C), prscDescLocal, (unsigned)PRSC_DescType::sync);    
    Value *PRSCpSync = gotStolenB.CreateBitCast(PRSCSync, SyncType::get(C)->getPointerTo()); 
    Constant *PRSC_DEC_JOIN = Get_PRSC_DEC_JOIN(*M);    
    gotStolenB.CreateCall(PRSC_DEC_JOIN, PRSCpSync);
    
    //TODO:
    // Check if counter is zero    
    Constant *PRSC_CHECKIFZERO_RESUME = Get_PRSC_CHECKIFZERO_RESUME(*M);
    Value * checkCounter = gotStolenB.CreateCall(PRSC_CHECKIFZERO_RESUME, PRSCpSync);
    checkCounter->dump();
    checkCounter->getType()->dump();
    Value * checkCntRes = gotStolenB.CreateICmpEQ(checkCounter, ConstantInt::get(Int32Ty, 1, /*isSigned=*/false) );
    
    BasicBlock * ifCounterZero = BasicBlock::Create(C, "CounterZero", F);
    BasicBlock * ifCounterNotZero = BasicBlock::Create(C, "CounterNotZero", F);

    gotStolenB.CreateCondBr(checkCntRes, ifCounterZero, ifCounterNotZero);
    gotStolenB.SetInsertPoint(ifCounterZero);    
    
    // TODO : This is NULL
    //gotStolenB.CreateBr(SyncBBMap[F]);
    gotStolenB.CreateUnreachable();
    CounterZeroBBVec.push_back(ifCounterZero);

    gotStolenB.SetInsertPoint(ifCounterNotZero);
    Constant *PRSC_SUSPEND_ROUTINE = Get_PRSC_SUSPEND_ROUTINE(*M);
    gotStolenB.CreateCall(PRSC_SUSPEND_ROUTINE);
    gotStolenB.CreateUnreachable();

    // Suspend for now

    while(tmpLevel > 0){
        gotStolenArr[detachLevel-tmpLevel+1] = BasicBlock::Create(C, "gotStolen", F); 
        
        gotStolenB.SetInsertPoint(gotStolenArr[detachLevel-tmpLevel+1]);
        if(storeInstArr[detachLevel]){
            Instruction* stInst = storeInstArr[detachLevel]->clone();
            stInst->setName(storeInstArr[detachLevel]->getName());
            gotStolenB.Insert(stInst, stInst->getName());
        }
        Value * PRSCSync  = gotStolenB.CreateStructGEP(PRSC_DescType::get(C), prscDescLocal, (unsigned)PRSC_DescType::sync);    
        Value *PRSCpSync = gotStolenB.CreateBitCast(PRSCSync, SyncType::get(C)->getPointerTo()); 
        Constant *PRSC_DEC_JOIN = Get_PRSC_DEC_JOIN(*M);
        gotStolenB.CreateCall(PRSC_DEC_JOIN, PRSCpSync);


        Constant *PRSC_CHECKIFZERO_RESUME = Get_PRSC_CHECKIFZERO_RESUME(*M);
        Value * checkCounter = gotStolenB.CreateCall(PRSC_CHECKIFZERO_RESUME, PRSCpSync);
        Value * checkCntRes = gotStolenB.CreateICmpEQ(checkCounter, ConstantInt::get(Int32Ty, 1, /*isSigned=*/false) );
        
        BasicBlock * ifCounterZero = BasicBlock::Create(C, "CounterZero", F);
        BasicBlock * ifCounterNotZero = BasicBlock::Create(C, "CounterNotZero", F);
        
        gotStolenB.CreateCondBr(checkCntRes, ifCounterZero, ifCounterNotZero);
        gotStolenB.SetInsertPoint(ifCounterZero);    
        //gotStolenB.CreateBr(SyncBBMap[F]);
        gotStolenB.CreateUnreachable();
        CounterZeroBBVec.push_back(ifCounterZero);

        gotStolenB.SetInsertPoint(ifCounterNotZero);        
        Constant *PRSC_SUSPEND_ROUTINE = Get_PRSC_SUSPEND_ROUTINE(*M);
        gotStolenB.CreateCall(PRSC_SUSPEND_ROUTINE);    
        gotStolenB.CreateUnreachable();

        tmpLevel--;
    }
    
    
    //TODO:
    // Create FSM for choosing which work to send
    BasicBlock * ifTrue = BasicBlock::Create(C, "TrueBB", F);
    BasicBlock * ifFalse = BasicBlock::Create(C, "FalseBB", F);
    static IRBuilder<> workFSMB(seedGeneration);
    
    using AsmPrototype = int (void);
    FunctionType *FAsmTy =
        TypeBuilder<AsmPrototype, false>::get(workFSMB.getContext());

    Value *Asm = InlineAsm::get(FAsmTy,
                              "movl %edi, $0\0A\09",
                              "=r,~{dirflag},~{fpsr},~{flags}",
                              /*sideeffects*/ true);

    //%73 = call i32 asm sideeffect "movl %edi, $0\0A\09", "=r,~{dirflag},~{fpsr},~{flags}"() #8, !dbg !2205, !srcloc !2206
    Value * bSuspendType = workFSMB.CreateCall(Asm);

    Value * PRSCSP  = workFSMB.CreateStructGEP(PRSC_DescType::get(C), prscDescLocal, (unsigned)PRSC_DescType::sp);
    
    pRA = workFSMB.CreateLoad(IntegerType::getInt8Ty(C)->getPointerTo(), PRSCSP);

    BlockAddress* bA = BlockAddress::get(detachBlock);   
    Value * cmpRes = workFSMB.CreateICmpEQ(bA,pRA);
    workFSMB.CreateCondBr(cmpRes, ifTrue, ifFalse);
 
    workFSMB.SetInsertPoint(ifTrue);

    Value *Val = ConstantInt::get(Int32Ty, detachLevel+2, /*isSigned=*/false);
    PRSCSync  = workFSMB.CreateStructGEP(PRSC_DescType::get(C), prscDescLocal, (unsigned)PRSC_DescType::sync);
    PRSCpSync = workFSMB.CreateBitCast(PRSCSync, SyncType::get(C)->getPointerTo()); 

    Constant *PRSC_SET_JOIN = Get_PRSC_SET_JOIN(*M);
    workFSMB.CreateCall(PRSC_SET_JOIN, {PRSCpSync, Val});



    bA = BlockAddress::get(gotStolenArr[0]);
    Value * ppRA = workFSMB.CreateBitCast(pRA, pRA->getType()->getPointerTo());
    workFSMB.CreateStore(bA, ppRA);

    if(genWorkBB[detachLevel])
        workFSMB.CreateBr(genWorkBB[detachLevel]);

    workFSMB.SetInsertPoint(ifFalse);
    
    tmpLevel = detachLevel;
    while(tmpLevel > 0){
        BlockAddress* bA = BlockAddress::get(gotStolenArr[detachLevel-tmpLevel]);
        
        BasicBlock * ifTrue = BasicBlock::Create(C, "TrueBB", F);
        BasicBlock * ifFalse = BasicBlock::Create(C, "FalseBB", F);
  
        Value * cmpRes = workFSMB.CreateICmpEQ(bA,pRA);
        workFSMB.CreateCondBr(cmpRes, ifTrue, ifFalse);
           
        workFSMB.SetInsertPoint(ifTrue);
        
        if(gotStolenArr[detachLevel-tmpLevel+1]){
            bA = BlockAddress::get(gotStolenArr[detachLevel-tmpLevel+1]);
            Value * ppRA = workFSMB.CreateBitCast(pRA, pRA->getType()->getPointerTo());
            workFSMB.CreateStore(bA, ppRA);
        }

        if(genWorkBB[tmpLevel-1])          
            workFSMB.CreateBr(genWorkBB[tmpLevel-1]);
        

        workFSMB.SetInsertPoint(ifFalse);
        lastFalseBB = ifFalse;

        tmpLevel--;
    }

#if 0
    //TODO :
    // Should I create the parallel path?
    // Parallel path
    bbV2Clone.clear();
    bbList.clear();
    haveVisited.clear();
    bb = nullptr;
    term = nullptr;
    bIgnore = false;
    
    // Search 
    bbList.push_back(Continue);
    bbList.push_back(detachBlock);
    while(!bbList.empty()){
        bb = bbList.back();
        bbList.pop_back();
        if ( (haveVisited.lookup(bb)) ){
            continue;
        }
        haveVisited[bb] = true;

        if ( (term = dyn_cast<DetachInst>(bb->getTerminator())) ){
            bbV2Clone.push_back(bb);
        } else if ( (term = dyn_cast<SyncInst>(bb->getTerminator())) ){
            bbV2Clone.push_back(bb);
        } else {
            bbV2Clone.push_back(bb);
            for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
                bbList.push_back(*SI);
            }
        }
    }
    

    // Work generation for thief
    if(!bIgnore){
        DEBUG(dbgs() << "\nparallel path start-----------------\n " );

        for(auto BB : bbV2Clone){
            // Clone this basic block
            // modify the following instruction
            // detach->br det.achd
            // reattach->remove
            // In detach block, remove store. Change call to send instr.

            // Create a new basic block and copy instructions into it!
            BasicBlock *bbC = CloneBasicBlock(BB, VMap, ".parallelPath", F, nullptr,
                                      nullptr);
                        
            
        }
        DEBUG(dbgs() << "\nparallel path end-----------------\n " );
    }
#endif

   IRBuilder<> builder(&*detachBlock->getFirstInsertionPt());
   Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
   
   // Do the potential jump later instead
   Value * seedGen = builder.CreateBitCast(Detach.getParent()->getParent(), VoidPtrTy);

   //Value * seedGen = builder.CreateBitCast(seedGeneration, VoidPtrTy);
   //seedGen = builder.CreateBitCast(seedGen, VoidPtrTy);
   //seedGen = builder.CreateBitCast(seedGen, VoidPtrTy);
   //builder.CreateCall(potentialJump, {seedGen});
    
   BranchInst *DetachBr = BranchInst::Create(detachBlock);   
   Instruction * reattach = Detach.getDetached()->getTerminator();
   BranchInst *ContinueBr = BranchInst::Create(Continue);
   //ReplaceInstWithInst(&Detach, DetachBr);
   //ReplaceInstWithInst(reattach, ContinueBr);
   
   detachLevel++;
    
  return nullptr;
}


void ULIABI::preProcessFunction(Function &F) {
  if (F.getName() != "fib") return;

  detachLevel = 0;

  llvm::errs() << "preprocessing " << F.getName() << "...\n";

  LLVMContext &C = F.getContext();
  Module *M = F.getParent();
  const DataLayout &DL = M->getDataLayout();
  auto InternalLinkage = Function::LinkageTypes::InternalLinkage;

  Type *VoidTy = TypeBuilder<void, false>::get(C);
  Type *VoidPtrTy = TypeBuilder<void*, false>::get(C);

  FunctionType *FTy = F.getFunctionType();
  assert(!FTy->isFunctionVarArg());

  Type *RetType = FTy->getReturnType();
  Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);
  Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
  Type *UliArgTypeTy = TypeBuilder<UliArgType, false>::get(C);
  // TODO: how to see if a type can fit in a 64bit register
  assert(RetType == Int32Ty || RetType == Int64Ty);

  Type *WorkPtrTy = TypeBuilder<Work*, false>::get(C);
  
  BasicBlock & entry  = F.getEntryBlock();
  IRBuilder<> B(entry.getFirstNonPHIOrDbgOrLifetime());
  Type *PRSC_DescTy = PRSC_DescType::get(C);
  prscDescLocal = B.CreateAlloca(PRSC_DescTy, DL.getAllocaAddrSpace(), nullptr, "PRSC_Dec");


  Function *Inlet = nullptr;
  // Inlet
  {
    FunctionType *InletTy = FunctionType::get(VoidTy, {Int32Ty, UliArgTypeTy, WorkPtrTy, Int32Ty}, /*isVarArg=*/false);
    auto Name = "__prsc_" + F.getName() + "Inlet";
    Inlet = Function::Create(InletTy, InternalLinkage, Name, M);
    Inlet->setCallingConv(CallingConv::X86_ULI);
    BasicBlock *Entry = BasicBlock::Create(C, "entry", Inlet);
    IRBuilder<> B(Entry);

    Argument &FromArg = Inlet->arg_begin()[0];
    Argument &Result = Inlet->arg_begin()[1];
    Argument &WorkPtr = Inlet->arg_begin()[2];
    Argument &From2Arg = Inlet->arg_begin()[3];

    // TODO: assert equal?
    // Value *FromMatch = B.CreateICmpEQ(&FromArg, &From2Arg);

    Constant *PRSC_DEC_JOIN = Get_PRSC_DEC_JOIN(*M);
    
    
    Value *WorkPSync = LoadSTyField(B, DL, WorkType::get(C), &WorkPtr, WorkType::pSync);
    B.CreateCall(PRSC_DEC_JOIN, WorkPSync);

    Value *ResultPtr = LoadSTyField(B, DL, WorkType::get(C), &WorkPtr, WorkType::res);

    // TODO:Alignment?
    StoreInst *S = B.CreateStore(&Result, ResultPtr);

    B.CreateRetVoid();

    //Inlet->dump();
  }

  // Wrapper function
  {
    SmallVector<Type *, 8> WrapperParamTys(FTy->param_begin(), FTy->param_end());
    WrapperParamTys.insert(WrapperParamTys.begin(), WorkPtrTy);

    FunctionType *WrapperFTy = FunctionType::get(VoidTy, WrapperParamTys, /*isVarArg=*/false);

    auto Name = "__prsc_" + F.getName() + "Wrapper";

    Function *Wrapper = Function::Create(WrapperFTy, InternalLinkage, Name, M);
    
    BasicBlock *Entry = BasicBlock::Create(C, "entry", Wrapper);

    IRBuilder<> B(Entry);
    Function::arg_iterator SecondArg = Wrapper->arg_begin(); ++SecondArg;
    SmallVector<Value*, 8> Args;
    for (auto it = SecondArg; it < Wrapper->arg_end(); ++it) {
      Args.push_back(it);
    }

    Value *Result = B.CreateCall(&F, Args, "result");


    // TODO: should this be a builtin instead??
    Constant *ENAULI = Get_ENAULI(*M);

    Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);

    B.CreateCall(ENAULI, { NEG_ZERO });


    Value *Work = Wrapper->arg_begin();
    Value *WorkSrc = LoadSTyField(B, DL, WorkType::get(C), Work, WorkType::src);
    Value *Zero = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
    Value *InletPtr = B.CreateBitCast(Inlet, VoidPtrTy);
    Value *SendResult = B.CreateZExtOrBitCast(Result, UliArgTypeTy);
    Value *SendWork = B.CreatePtrToInt(Work, UliArgTypeTy);

    Constant *threadIdGlobal = M->getOrInsertGlobal("threadId", Int32Ty);
    assert(threadIdGlobal);
    Value *threadId = B.CreateLoad(threadIdGlobal, "threadId");

    Function *UliSend = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_send);

    // TODO: use fibInlet instead of NullPtr
    B.CreateCall(UliSend, {WorkSrc, Zero, InletPtr, SendResult, SendWork, threadId});

    B.CreateRetVoid();
    
    // Store the wrapper function
    WrapperMap[&F] =  Wrapper;

    //Wrapper->dump();
    //F.dump();
  }
  
  // Seed Generation
  {
    B.SetInsertPoint(F.getEntryBlock().getTerminator());
    seedLocal = B.CreateAlloca(SeedType::get(C), DL.getAllocaAddrSpace(), nullptr, "seed");
    seedGeneration = BasicBlock::Create(C, "seedGen", &F);
    
    B.SetInsertPoint(seedGeneration);

    // Fix the rbp first using the rsp
    Function *SetupRBPfromRSPinRBP = Intrinsic::getDeclaration(M, Intrinsic::x86_setup_rbp_from_sp_in_rbp);
    B.CreateCall(SetupRBPfromRSPinRBP);
    
  }
  
  // Sync Resume
  {
    syncResumeBB = BasicBlock::Create(C, "syncResume", &F);
    B.SetInsertPoint(syncResumeBB); B.CreateUnreachable();


  }
  // TODO : Finish the here is work handler
  // Here is work Handler
  {
   SmallVector<Type *, 8> WorkHandlerParamTys(FTy->param_begin(), FTy->param_end());
   WorkHandlerParamTys.insert(WorkHandlerParamTys.begin(), VoidPtrTy);
   WorkHandlerParamTys.push_back(VoidPtrTy);
   WorkHandlerParamTys.push_back(VoidPtrTy);
   WorkHandlerParamTys.push_back(SyncType::get(C)->getPointerTo());
   WorkHandlerParamTys.push_back(VoidPtrTy);

   FunctionType *WorkHandlerFTy = FunctionType::get(VoidTy, WorkHandlerParamTys, /*isVarArg=*/false);

   auto Name = "__prsc_" + F.getName() + "HereIsWorkHandler";
   
   Function *HereIsWorkHandler = Function::Create(WorkHandlerFTy, InternalLinkage, Name, M);
   
   HereIsWorkHandler->addFnAttr(Attribute::UserLevelInterrupt);
   
   BasicBlock *Entry = BasicBlock::Create(C, "entry", HereIsWorkHandler);
   
   IRBuilder<> B(Entry);   

   using AsmPrototype = int (void);
   FunctionType *FAsmTy =
       TypeBuilder<AsmPrototype, false>::get(C);

   Value *Asm = InlineAsm::get(FAsmTy,
                              "movl %rdi, $0\0A\09",
                              "=r,~{dirflag},~{fpsr},~{flags}",
                              /*sideeffects*/ true);

   //%73 = call i32 asm sideeffect "movl %edi, $0\0A\09", "=r,~{dirflag},~{fpsr},~{flags}"() #8, !dbg !2205, !srcloc !2206
   Value * from = B.CreateCall(Asm);
   //Value * from = ONE;


   Constant *PRSC_RESET_WORKSTEAL = Get_PRSC_RESET_WORKSTEAL(*M);
   B.CreateCall(PRSC_RESET_WORKSTEAL);

   
   Value * fp = HereIsWorkHandler->arg_begin();   
   Value * res = HereIsWorkHandler->arg_end()-1;
   Value * sync = HereIsWorkHandler->arg_end()-2;
   Value * parentSP = HereIsWorkHandler->arg_end()-3;
   Value * parentIP = HereIsWorkHandler->arg_end()-4;   
   Value * realArgStart = HereIsWorkHandler->arg_begin() + 1;
   
   int numArgs = HereIsWorkHandler->arg_end()-HereIsWorkHandler->arg_begin();
   int realNumArgs = numArgs - 5;// Remove fp, res, syn, parentSP/IP


   Value * ARGC =  ConstantInt::get(Int32Ty, realNumArgs, /*isSigned=*/false);
   Value * ONE =  ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);
  
   // TODO : fix this-> lowering of uli_message_from happens earlier than this.    
   //Function *UliFrom = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_message_from);   
   //Value * from = B.CreateCall(UliFrom);
      
   // Check if fp is NULL
   BasicBlock * fpIsNotNull = BasicBlock::Create(C, "fpIsNotNull", HereIsWorkHandler);
   BasicBlock * fpIsNull = BasicBlock::Create(C, "fpIsNull", HereIsWorkHandler);
   Value * isFpNull = B.CreateICmpEQ(fp, ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo()) );
   
   B.CreateCondBr(isFpNull, fpIsNull, fpIsNotNull);
   B.SetInsertPoint(fpIsNotNull);      

   //Constant *PRSC_CREATE_WORK = Get_PRSC_CREATE_WORK(*M);
   
   Constant *PRSC_CREATE_WORK = M->getOrInsertFunction("PRSC_CREATE_WORK", WorkType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C), IntegerType::getInt32Ty(C), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), SyncType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C)); 


   Value * potentialWork = B.CreateCall(PRSC_CREATE_WORK, {fp, ARGC, from, parentIP, parentSP, sync, res, ONE});
   

#if 1

   for(int ii = 0; ii<realNumArgs; ii++){
       Value * v = realArgStart+ii;
       // Check type
       if(v->getType()->isIntegerTy()){
           errs() << "Value of potentialWork type\n";
           potentialWork->dump();
           potentialWork->getType()->dump();

           Value * pargv  = B.CreateStructGEP(WorkType::get(C), potentialWork, (unsigned)WorkType::argv);    
           errs() << "Value of pargv type\n";
           pargv->dump();
           pargv->getType()->dump();

           Value * argv = B.CreateLoad(IntegerType::getInt64Ty(C)->getPointerTo(), pargv);           
           errs() << "Value of argv type\n";
           argv->dump();
           argv->getType()->dump();
           
           Value * storeArg = B.CreateInBoundsGEP( IntegerType::getInt64Ty(C), argv, ConstantInt::get(Int32Ty, ii, /*isSigned=*/false) );
           errs() << "Value of firstStoreArg\n";
           storeArg->dump();
           storeArg->getType()->dump();
           
           Value * zext = B.CreateZExt(v, IntegerType::getInt64Ty(C), "t5");
           errs() << "Value of v\n";
           v->dump();
           v->getType()->dump();
           B.CreateStore(zext, storeArg);

           errs() << "End\n";
       } else if (v->getType()->isPointerTy()){ 
           errs() << "Value of potentialWork type\n";
           potentialWork->dump();
           potentialWork->getType()->dump();

           Value * pargv  = B.CreateStructGEP(WorkType::get(C), potentialWork, (unsigned)WorkType::argv);    
           errs() << "Value of pargv type\n";
           pargv->dump();
           pargv->getType()->dump();

           Value * argv = B.CreateLoad(IntegerType::getInt64Ty(C)->getPointerTo(), pargv);           
           errs() << "Value of argv type\n";
           argv->dump();
           argv->getType()->dump();
           
           Value * storeArg = B.CreateInBoundsGEP( IntegerType::getInt64Ty(C), argv, ConstantInt::get(Int32Ty, ii, /*isSigned=*/false) );
           errs() << "Value of firstStoreArg\n";
           storeArg->dump();
           storeArg->getType()->dump();
           
           Value * zext = B.CreateCast(Instruction::PtrToInt, v, IntegerType::getInt64Ty(C));

           errs() << "Value of v\n";
           v->dump();
           v->getType()->dump();
           B.CreateStore(zext, storeArg);
       } else {
           assert(false && "Type not yet supported");
       }
              
   }
#endif 

   Constant * PRSC_PUSHFRONT_WORKQ = Get_PRSC_PUSHFRONT_WORKQ(*M);
   B.CreateCall(PRSC_PUSHFRONT_WORKQ, potentialWork);

   B.CreateRetVoid();
   
   B.SetInsertPoint(fpIsNull);
   B.CreateRetVoid();
    
   // Store the here is work handler function
   WorkReplyHandlerMap[&F] =  HereIsWorkHandler;

   
  }

  //F.dump();
  

  //assert(false);
}

void ULIABI::postProcessFunction(Function &F) {
    
    LLVMContext &C = F.getContext();
    Module *M = F.getParent();
    const DataLayout &DL = M->getDataLayout();
    
    // For pushing and popping the seed 
    //-=======================================================================
    Constant *PRSC_PUSHFRONT_SEEDQ = Get_PRSC_PUSHFRONT_SEEDQ(*M);
    Constant *PRSC_POPFRONT_SEEDQ = Get_PRSC_POPFRONT_SEEDQ(*M);
    
    Function *GetSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);
    
    IRBuilder<> B(firstDetach->getTerminator());
    //B.SetInsertPoint(firstDetach->getTerminator());
    Value * currSp = B.CreateCall(GetSP);    
    Value * pSeedSP  = B.CreateStructGEP(SeedType::get(C), seedLocal, (unsigned)SeedType::sp);    
    currSp = B.CreateBitCast(pSeedSP, TypeBuilder<void*, false>::get(C));

    Value * seedStoreSp = B.CreateStore(currSp, pSeedSP);
    
    Value * seedIP  = B.CreateStructGEP(SeedType::get(C), seedLocal, (unsigned)SeedType::ip);    
    BlockAddress* seedGenAddr = BlockAddress::get(seedGeneration);


    Value * seedStoreIp = B.CreateStore(seedGenAddr, seedIP);
    Value * pSeedLocal = B.CreateBitCast(seedLocal, SeedType::get(C)->getPointerTo());
    B.CreateCall(PRSC_PUSHFRONT_SEEDQ, pSeedLocal);

    B.SetInsertPoint(lastDetach->getTerminator());
    B.CreateCall(PRSC_POPFRONT_SEEDQ);
    
    // For the sync resume
    //-======================================================================
    B.SetInsertPoint(syncResumeBB);    
    Instruction * syncTerm = syncResumeBB->getTerminator();
    
    // Fix base pointer
    Function *SetupRBPfromRSP = Intrinsic::getDeclaration(M, Intrinsic::x86_setup_rbp_from_rsp);
    B.CreateCall(SetupRBPfromRSP);

    // Branch to the sync
    B.CreateBr(SyncBBMap[&F]);
    
    // Delete the previous terminator instruction
    syncTerm->eraseFromParent();
    
    // For gotStolen
    //-==================================================================
    for( auto BB : CounterZeroBBVec ){
        Instruction * term  = BB->getTerminator();
        B.SetInsertPoint(term);
        B.CreateBr(SyncBBMap[&F]);
        term->eraseFromParent();
    }

    //assert(false);
}

void ULIABI::postProcessHelper(Function &F) {
    //assert(false);
}

bool ULIABILoopSpawning::processLoop() {
    //assert(false);
  return false;
}

ULIABI::ULIABI() {}

