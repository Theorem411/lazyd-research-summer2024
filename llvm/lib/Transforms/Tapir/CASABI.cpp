//===- CASABI.cpp - Lower Tapir into CAS PRSC runtime system calls -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the CAS ABI to convert Tapir instructions to calls
// into the user-level-interrupts PRSC library.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Tapir/CASABI.h"
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
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/Tapir/Outline.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/EscapeEnumerator.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/TapirUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

//TODO : Code refactoring
//TODO : Design document

using namespace llvm;

#define DEBUG_TYPE "uliabi"


#define MAX_LEVEL 8
// Store instruction to store the result of the potential parallel call 
StoreInst  * gStInstArr_cas[MAX_LEVEL];

//  Basic block for generating work
BasicBlock * gGenWorkBBArr_cas[MAX_LEVEL];

// Entry point for generating work
BasicBlock *  gGenWorkEntryBB_cas;

BasicBlock * gLastFalseBB_cas[MAX_LEVEL];
BasicBlock * gFirstDetachBB_cas[MAX_LEVEL];
BasicBlock * gLastDetachBB_cas[MAX_LEVEL];
BasicBlock * gSyncResumeBB_cas[MAX_LEVEL];

BasicBlock * oldDetachBB_cas = nullptr;
BlockAddress * oldBA_cas = nullptr;

Value * gPrscDescLocalVar_cas;
Value * gSeedLocalVar_cas;

// Check if we should jump to the suspend routine or to steal routine
Value * gIsSuspend_cas;
Value * gWork_cas;

// Store basic block that is taken if the join counter == 0 (Basic block is basically a jump to sync statement
SmallVector<BasicBlock *, 8> gCntEqZeroBBList_cas;
DenseMap<BasicBlock *, int> gBBtoSyncLevel_cas;

// A map that maps a function to the wrapper function and the here is work reply handler
// TODO : Combine the below map into one single map <Function * , ArrayofFunction>
DenseMap<Function *, Function *> gWrapperMap_cas;
DenseMap<Function *, Function *> gRemoteInletMap_cas;
DenseMap<Function *, Function *> gLocalInletMap_cas;
DenseMap<Function *, Function *> gRecvWorkHandlerMap_cas;

// Store the basic block that is executed after the cilk_sync statment
//DenseMap<Function *, BasicBlock *> gSyncBBMap_cas;
BasicBlock * gSyncBBMap_cas[MAX_LEVEL];

unsigned detachLevel_cas = 0;

unsigned syncLevel_cas =0;

unsigned gSlvlI_cas = 0;


ValueToValueMapTy VMap; 

using Sync = CASABI::Sync;
using Work = CASABI::Work;
using PRSC_Desc = CASABI::PRSC_Desc;
using Seed = CASABI::Seed;


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

using POLL_ty = void (unsigned );
DEFAULT_GET_LIB_FUNC(POLL)

using PRSC_DEC_JOIN_ty = void (Sync*);
DEFAULT_GET_LIB_FUNC(PRSC_DEC_JOIN)

using PRSC_CHECKIFZERO_RESUME_ty = int (Sync*);
DEFAULT_GET_LIB_FUNC(PRSC_CHECKIFZERO_RESUME)

using PRSC_RESET_WORKSTEAL_ty = void (unsigned int);
DEFAULT_GET_LIB_FUNC(PRSC_RESET_WORKSTEAL)

using PRSC_POPFRONT_SEEDQ_ty = void (void);
DEFAULT_GET_LIB_FUNC(PRSC_POPFRONT_SEEDQ)

using PRSC_PUSHFRONT_SEEDQ_ty = void (Seed*);
DEFAULT_GET_LIB_FUNC(PRSC_PUSHFRONT_SEEDQ)

using PRSC_SET_JOIN_ty = void (Sync*, int);
DEFAULT_GET_LIB_FUNC(PRSC_SET_JOIN)

using PRSC_SUSPEND_ROUTINE_ty = void (void);
DEFAULT_GET_LIB_FUNC(PRSC_SUSPEND_ROUTINE)

using PRSC_SUSPEND_AND_CHANGERETADDR_ty = void (void *);
DEFAULT_GET_LIB_FUNC(PRSC_SUSPEND_AND_CHANGERETADDR)

using PRSC_RESUME_TO_HANDLER_ty = void (int );
DEFAULT_GET_LIB_FUNC(PRSC_RESUME_TO_HANDLER)

using PRSC_PUSHFRONT_WORKQ_ty = void (Work*);
DEFAULT_GET_LIB_FUNC(PRSC_PUSHFRONT_WORKQ)

using PRSC_PUSHFRONT_READYQ_ty = void (void *, void*);
DEFAULT_GET_LIB_FUNC(PRSC_PUSHFRONT_READYQ)

using PRSC_END_WORK_ty = void (Work *);
DEFAULT_GET_LIB_FUNC(PRSC_END_WORK)

using PRSC_PUSHFRONT_CONTQ_ty = void (Work *);
DEFAULT_GET_LIB_FUNC(PRSC_PUSHFRONT_CONTQ)


using PRSC_INIT_RT_ty = void (void);
DEFAULT_GET_LIB_FUNC(PRSC_INIT_RT)

using PRSC_DEINIT_RT_ty = void (void);
DEFAULT_GET_LIB_FUNC(PRSC_DEINIT_RT)

using PRSC_SHOW_STATS_ty = void (void);
DEFAULT_GET_LIB_FUNC(PRSC_SHOW_STATS)

typedef void* (*FP)(void);
using Scalar = long long int;
using UliArgType = long long int;

// Build type for Sync structure
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

// Build type for Work structure
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
        TypeBuilder<Scalar*, X>::get(C), // argv
        TypeBuilder<FP, X>::get(C), // fp
        TypeBuilder<int, X>::get(C), // id
        TypeBuilder<uint, X>::get(C), // argc
        TypeBuilder<Scalar*, X>::get(C), // res
        TypeBuilder<Sync*, X>::get(C), // pSync
        TypeBuilder<Work*, X>::get(C), // next
        TypeBuilder<Work*, X>::get(C), // prev
        TypeBuilder<int, X>::get(C), // stolen
        TypeBuilder<int, X>::get(C), // realized
        TypeBuilder<unsigned int, X>::get(C),  // src
        TypeBuilder<void*, X>::get(C),  // sp
        TypeBuilder<void*, X>::get(C)  // ip
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
    argv,
    fp,
    id,
    argc,
    res,
    pSync,
    next,
    prev,
    stolen,
    realized,
    src,
    sp,
    ip
  };
};
}
using WorkType = TypeBuilder<Work, false>;

// Build type for PRSC_Desc
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

// Build type for seed structure
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

Value *CASABI::lowerGrainsizeCall(CallInst *GrainsizeCall) {
  assert(false);
  return nullptr;
}

void CASABI::createSync(SyncInst &SI, ValueToValueMapTy &DetachCtxToStackFrame) {    
    SI.dump();
    SyncInst* syncClone = dyn_cast<SyncInst>(VMap[&SI]);
    
    BasicBlock * curBB = SI.getParent();
    Function * F = curBB->getParent();
    Module * M = F->getParent();
    LLVMContext& C = M->getContext();
    
    BasicBlock * bb = nullptr;
    Instruction * term = nullptr;
    
    // Build type
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);


    if(syncClone)
        syncClone->dump();
    
    // Fast Path
    // ----------------------------------------------
    {
        BasicBlock * succ = SI.getSuccessor(0);
    }

    // Slow Path
    // ---------------------------------------------
    {

        // clone of syncBB will become the steal request handler
        
        SmallVector<BasicBlock*, 8> bbList;
        DenseMap<BasicBlock *, bool> haveVisited;
        
        BasicBlock * syncBB = syncClone->getParent();
        Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);
        Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);
        Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  
        Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  

        IRBuilder<> slowBuilder( syncBB->getTerminator()  );
        slowBuilder.CreateCall(disuli, {ZERO});


        // Look for the reattach inst
        // Add an epilogue just before it
        bbList.push_back(syncBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator() ))  ){
                // Don't push anymore if we encountered reattach instruction
                ReattachInst * reattachInst = dyn_cast<ReattachInst>( bb->getTerminator() );
                BasicBlock   * startOfStealHandler = reattachInst->getDetachContinue();
                slowBuilder.SetInsertPoint( startOfStealHandler->getFirstNonPHIOrDbgOrLifetime() );
                slowBuilder.CreateCall(enauli, {NEG_ZERO});
            } else {
                for( pred_iterator PI = pred_begin(bb); PI!=pred_end(bb); PI++ ){                
                    bbList.push_back(*PI);
                }
            }
        }

    }
    
    return;
}

void CASABI::SetJoinCounter(IRBuilder <> & B, int val, Module * M, LLVMContext & C){
    Type * Int32Ty = TypeBuilder<int32_t, false>::get(C);
    Value *Val = ConstantInt::get(Int32Ty, detachLevel_cas+2, /*isSigned=*/false);
    Value * PRSCpSync  = B.CreateStructGEP(PRSC_DescType::get(C), gPrscDescLocalVar_cas, (unsigned)PRSC_DescType::sync);
    Constant *PRSC_SET_JOIN = Get_PRSC_SET_JOIN(*M);
    B.CreateCall(PRSC_SET_JOIN, {PRSCpSync, Val});
}


void CASABI::DecrementJoinCounter(IRBuilder <> & gotStolenB, Module * M, LLVMContext & C){
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  
    Value * PRSCpSync  = gotStolenB.CreateStructGEP(PRSC_DescType::get(C), gPrscDescLocalVar_cas, (unsigned)PRSC_DescType::sync);    
    Constant *PRSC_DEC_JOIN = Get_PRSC_DEC_JOIN(*M);
    Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);    
    gotStolenB.CreateCall(disuli, { ZERO });
    gotStolenB.CreateCall(PRSC_DEC_JOIN, PRSCpSync);
    
}

Value* CASABI::CheckIfJoinCounterZero(IRBuilder <> & gotStolenB, Module * M, LLVMContext & C){
    Type * Int32Ty = TypeBuilder<int32_t, false>::get(C);
    Value * ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);
    Value * PRSCpSync  = gotStolenB.CreateStructGEP(PRSC_DescType::get(C), gPrscDescLocalVar_cas, (unsigned)PRSC_DescType::sync);    
    Constant *PRSC_CHECKIFZERO_RESUME = Get_PRSC_CHECKIFZERO_RESUME(*M);
    Value * checkCounter = gotStolenB.CreateCall(PRSC_CHECKIFZERO_RESUME, PRSCpSync);
    Value * checkCntRes = gotStolenB.CreateICmpEQ(checkCounter, ONE);
    return checkCntRes;

}

void CASABI::StoreFuncRes(IRBuilder <> & gotStolenB, int detachLevel_cas, LLVMContext & C){
    // TODO: fix this
    if(gStInstArr_cas[detachLevel_cas]){
        // Does not work, need asm
        //gotStolenB.Insert(gStInstArr_cas[detachLevel_cas], gStInstArr_cas[detachLevel_cas]->getName());
        Value * toStoreTo = gStInstArr_cas[detachLevel_cas]->getPointerOperand();

        using AsmPrototype = void ( int* );
        FunctionType *FAsmTy =
            TypeBuilder<AsmPrototype, false>::get(gotStolenB.getContext());

        Value *Asm = InlineAsm::get(FAsmTy,
                              "movl %eax, $0\0A\09",
                              "=*m,~{dirflag},~{fpsr},~{flags}",
                              /*sideeffects*/ true);

        // Store the result to storeInst
        gotStolenB.CreateCall(Asm, toStoreTo); 
    }
}


void CASABI::StoreRetInInlet(IRBuilder <> &B, Argument & Result, Argument & WorkPtr, Type* resTy, LLVMContext & C, const DataLayout &DL) {
    Value *ResultPtr = LoadSTyField(B, DL, WorkType::get(C), &WorkPtr, WorkType::res);
    if(resTy->isIntegerTy()){
        Value * result  = B.CreateZExtOrTrunc(&Result, resTy, "t5");
        Value * resultPtr  = B.CreateBitCast(ResultPtr, resTy->getPointerTo(), "t5");            
        // TODO:Alignment?
        StoreInst *S = B.CreateStore(result, resultPtr);
    } else if (resTy->isPointerTy()){
        assert(false && "Storing this type is not supported yet");
        //Value * result =  B.CreateCast(Instruction::IntToPtr, ppRA, IntegerType::getInt8Ty(C)->getPointerTo());
    } else if (resTy->isVoidTy()) {
        // Do nothing
        ;
    } else {
        assert(false && "Storing this type is not supported yet");
    }

}


void CASABI::PopulateAfterCheckCnt(IRBuilder <> &gotStolenB, BasicBlock * parentBB, Value * checkCntRes, DetachInst &Detach, Function * F, Module * M, LLVMContext & C){
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);

    BasicBlock * ifCounterZero = BasicBlock::Create(C, "CounterZero", F);    
    BasicBlock * ifCounterNotZero = BasicBlock::Create(C, "CounterNotZero", F);

    Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);
    Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false); 

    gotStolenB.CreateCondBr(checkCntRes, ifCounterZero, ifCounterNotZero);
    gotStolenB.SetInsertPoint(ifCounterZero);    
    
    // Fix later in the post processing
    gotStolenB.CreateCall(enauli, { NEG_ZERO });
    gotStolenB.CreateUnreachable();
    gCntEqZeroBBList_cas.push_back(ifCounterZero);
    gBBtoSyncLevel_cas[ifCounterZero] = syncLevel_cas-1;

    gotStolenB.SetInsertPoint(ifCounterNotZero);
    Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
    gotStolenB.CreateCall(potentialJump, {BlockAddress::get(gSyncResumeBB_cas[syncLevel_cas-1])});
    Constant *PRSC_SUSPEND_AND_CHANGERETADDR = Get_PRSC_SUSPEND_AND_CHANGERETADDR(*M);
    //gotStolenB.CreateCall(enauli, { NEG_ZERO });

    // Suspend for now
    
    CallInst * CI = CallInst::Create(PRSC_SUSPEND_AND_CHANGERETADDR, {BlockAddress::get(parentBB)});

    // TODO: Hack?
    CI->setDebugLoc(Detach.getDebugLoc());
    gotStolenB.Insert(CI);    
    gotStolenB.CreateUnreachable();
}

void CASABI::GenerateInletEntry(IRBuilder<> & B, Argument & Result, Argument & WorkPtr, Type * resTy, Function * Inlet, Module * M, LLVMContext & C, const DataLayout &DL){    
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);

    StoreRetInInlet(B, Result, WorkPtr, resTy, C, DL);

    Constant *PRSC_DEC_JOIN = Get_PRSC_DEC_JOIN(*M);    
    Value *WorkPSync = LoadSTyField(B, DL, WorkType::get(C), &WorkPtr, WorkType::pSync);
    B.CreateCall(PRSC_DEC_JOIN, WorkPSync);

    Constant *PRSC_CHECKIFZERO_RESUME = Get_PRSC_CHECKIFZERO_RESUME(*M);
    Value * checkCounter = B.CreateCall(PRSC_CHECKIFZERO_RESUME, WorkPSync);
    Value * checkCntRes = B.CreateICmpEQ(checkCounter, ConstantInt::get(Int32Ty, 1, /*isSigned=*/false) );
    
    BasicBlock * ifCounterZero = BasicBlock::Create(C, "CounterZero", Inlet);
    BasicBlock * ifCounterNotZero = BasicBlock::Create(C, "CounterNotZero", Inlet);

    B.CreateCondBr(checkCntRes, ifCounterZero, ifCounterNotZero);
    B.SetInsertPoint(ifCounterZero);    
        
    Constant *PRSC_PUSHFRONT_CONTQ = Get_PRSC_PUSHFRONT_CONTQ(*M);
    B.CreateCall(PRSC_PUSHFRONT_CONTQ, &WorkPtr);
    

    B.CreateRetVoid();

    B.SetInsertPoint(ifCounterNotZero);
    
    Constant *PRSC_END_WORK = Get_PRSC_END_WORK(*M);
    B.CreateCall(PRSC_END_WORK, &WorkPtr);

    Instruction * retVoid  = B.CreateRetVoid();
}

Function * CASABI::GenerateHereIsWorkHandlerFunc(Function & F, Module * M, LLVMContext & C){

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
    //assert(RetType == Int32Ty || RetType == Int64Ty);

    Type *WorkPtrTy = TypeBuilder<Work*, false>::get(C);
   
    SmallVector<Type *, 8> WorkHandlerParamTys(FTy->param_begin(), FTy->param_end());
    WorkHandlerParamTys.insert(WorkHandlerParamTys.begin(), VoidPtrTy);
    WorkHandlerParamTys.insert(WorkHandlerParamTys.begin(), WorkPtrTy);
    WorkHandlerParamTys.insert(WorkHandlerParamTys.begin(), Int64Ty);
    WorkHandlerParamTys.push_back(VoidPtrTy);
    WorkHandlerParamTys.push_back(VoidPtrTy);
    WorkHandlerParamTys.push_back(SyncType::get(C)->getPointerTo());
    WorkHandlerParamTys.push_back(VoidPtrTy);

    FunctionType *WorkHandlerFTy = FunctionType::get(VoidTy, WorkHandlerParamTys, /*isVarArg=*/false);

    auto Name = "__prsc_" + F.getName() + "HereIsWorkHandler";
   
    Function *HereIsWorkHandler = Function::Create(WorkHandlerFTy, InternalLinkage, Name, M);
    HereIsWorkHandler->setCallingConv(CallingConv::X86_ULI);
    HereIsWorkHandler->addFnAttr(Attribute::UserLevelInterrupt);
   
    BasicBlock *Entry = BasicBlock::Create(C, "entry", HereIsWorkHandler);
   
    IRBuilder<> B(Entry);   


    Value * from = HereIsWorkHandler->arg_begin();
    Value * replyWork = HereIsWorkHandler->arg_begin()+1;   
    Value * fp = HereIsWorkHandler->arg_begin()+2;   
    Value * res = HereIsWorkHandler->arg_end()-1;
    Value * sync = HereIsWorkHandler->arg_end()-2;
    Value * parentSP = HereIsWorkHandler->arg_end()-3;
    Value * parentIP = HereIsWorkHandler->arg_end()-4;   
    Value * realArgStart = HereIsWorkHandler->arg_begin() + 3;
   
    int numArgs = HereIsWorkHandler->arg_end()-HereIsWorkHandler->arg_begin();
    int realNumArgs = numArgs - 7;// Remove from, work, fp, res, syn, parentSP/IP

    Value * ARGC =  ConstantInt::get(Int32Ty, realNumArgs, /*isSigned=*/false);
    Value * ONE =  ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);

    Value * from32 = B.CreateTrunc(from, Int32Ty);
    Constant *PRSC_RESET_WORKSTEAL = Get_PRSC_RESET_WORKSTEAL(*M);
    B.CreateCall(PRSC_RESET_WORKSTEAL, from32);

  
    // Check if fp is NULL
    BasicBlock * fpIsNotNull = BasicBlock::Create(C, "fpIsNotNull", HereIsWorkHandler);
    BasicBlock * fpIsNull = BasicBlock::Create(C, "fpIsNull", HereIsWorkHandler);
    Value * isFpNull = B.CreateICmpEQ(fp, ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo()) );
   
    B.CreateCondBr(isFpNull, fpIsNull, fpIsNotNull);
    B.SetInsertPoint(fpIsNotNull);      

    Constant *PRSC_CREATE_WORK = M->getOrInsertFunction("PRSC_CREATE_WORK", WorkType::get(C)->getPointerTo(), WorkType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C), IntegerType::getInt64Ty(C), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), SyncType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C)); 

    Value * potentialWork = B.CreateCall(PRSC_CREATE_WORK, {replyWork, fp, ARGC, from, parentIP, parentSP, sync, res, ONE});

    StoreArgIntoWork(C, B, HereIsWorkHandler, 3, potentialWork, realNumArgs);

    Constant * PRSC_PUSHFRONT_WORKQ = Get_PRSC_PUSHFRONT_WORKQ(*M);
    B.CreateCall(PRSC_PUSHFRONT_WORKQ, potentialWork);
    
    //B.CreateRetVoid();
    B.CreateBr(fpIsNull);
   
    B.SetInsertPoint(fpIsNull);
    B.CreateRetVoid();

    return HereIsWorkHandler;
}

Function * CASABI::GenerateRemoteInlet(Function & F, Module * M, LLVMContext & C){
    Function * RemoteInlet = nullptr;
    
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
    //assert(RetType == Int32Ty || RetType == Int64Ty);

    Type *WorkPtrTy = TypeBuilder<Work*, false>::get(C);

    FunctionType *InletTy = FunctionType::get(VoidTy, {Int32Ty, UliArgTypeTy, WorkPtrTy, Int32Ty}, /*isVarArg=*/false);
    auto Name = "__prsc_" + F.getName() + "Remote_Inlet";
    RemoteInlet = Function::Create(InletTy, InternalLinkage, Name, M);
    RemoteInlet->addFnAttr(Attribute::UserLevelInterrupt);    
    RemoteInlet->setCallingConv(CallingConv::X86_ULI);
    //RemoteInlet->addFnAttr("disable_tail_calls");
    BasicBlock *Entry = BasicBlock::Create(C, "entry", RemoteInlet);
    IRBuilder<> B(Entry);
    

    Argument &FromArg = RemoteInlet->arg_begin()[0];
    Argument &Result = RemoteInlet->arg_begin()[1];
    Argument &WorkPtr = RemoteInlet->arg_begin()[2];
    Argument &From2Arg = RemoteInlet->arg_begin()[3];
     
    // TODO: assert equal?
    // Value *FromMatch = B.CreateICmpEQ(&FromArg, &From2Arg);
    
    GenerateInletEntry(B, Result, WorkPtr, RetType, RemoteInlet, M, C, DL);    
    

    gRemoteInletMap_cas[&F] =  RemoteInlet;

    return RemoteInlet;
}

//TODO :
// Free the work and its argument
// free(w); free(w->argv);
Function * CASABI::GenerateLocalInlet(Function & F, Module * M, LLVMContext & C){
    Function * localInlet = nullptr;

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
    //assert(RetType == Int32Ty || RetType == Int64Ty);

    Type *WorkPtrTy = TypeBuilder<Work*, false>::get(C);

    FunctionType *InletTy = FunctionType::get(VoidTy, {UliArgTypeTy, WorkPtrTy}, /*isVarArg=*/false);
    auto Name = "__prsc_" + F.getName() + "Local_Inlet";
    localInlet = Function::Create(InletTy, InternalLinkage, Name, M);
    BasicBlock *Entry = BasicBlock::Create(C, "entry", localInlet);
    IRBuilder<> B(Entry);
    // Generate the disuli here
    Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);
    Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  
    B.CreateCall(disuli, { ZERO });
    
    // Result is store later in the postProcess once we get the return type
    Argument &Result = localInlet->arg_begin()[0];
    Argument &WorkPtr = localInlet->arg_begin()[1];
 
    
    // TODO: assert equal?
    // Value *FromMatch = B.CreateICmpEQ(&FromArg, &From2Arg);
    
    GenerateInletEntry(B, Result, WorkPtr, RetType, localInlet, M, C, DL);    
    
    // Generate the enauli here
    for (auto &BB : *localInlet){
        Instruction * termInst = BB.getTerminator();
        if(isa<ReturnInst>(termInst)){
            B.SetInsertPoint(termInst);
            Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);
            Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);      
            B.CreateCall(enauli, { NEG_ZERO });
        }
    }
    
    errs() << "Key value : " << &F << "\n";
    gLocalInletMap_cas[&F] =  localInlet;
    //Inlet->dump();

    return localInlet;
}

Function * CASABI::GenerateWrapperFunc(Function & F, Module * M, LLVMContext & C){
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
    //assert(RetType == Int32Ty || RetType == Int64Ty);

    Type *WorkPtrTy = TypeBuilder<Work*, false>::get(C);
  
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

    Value *Result = B.CreateCall(&F, Args);
    if (RetType->isVoidTy()){
        Result =  ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
    }

    // TODO: should this be a builtin instead?? Fail on native using ENAULI
    Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);
    Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  

    B.CreateCall(enauli, { NEG_ZERO });

    Value *Work = Wrapper->arg_begin();
    Value * WorkStolen = LoadSTyField(B, DL, WorkType::get(C), Work, WorkType::stolen);
    Value *ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
    
    Value * SendResult = nullptr;
    Value * SendWork = B.CreatePtrToInt(Work, UliArgTypeTy);;
    
    if (RetType->isVoidTy()){
        SendResult = ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
        SendResult = B.CreatePtrToInt(SendResult, UliArgTypeTy);
    }else {
        SendResult = B.CreateZExtOrBitCast(Result, UliArgTypeTy);
    }

    BasicBlock *BBremoteInlet = BasicBlock::Create(C, "remoteInlet", Wrapper);
    BasicBlock *BBlocalInlet = BasicBlock::Create(C, "localInlet", Wrapper);
    Value * ifZero = B.CreateICmpEQ(WorkStolen, ZERO);
    B.CreateCondBr(ifZero, BBlocalInlet, BBremoteInlet);
    
    B.SetInsertPoint(BBlocalInlet);
    
    Function * localInlet = nullptr;
    if(gLocalInletMap_cas.count(&F) == 0){
        localInlet  = GenerateLocalInlet(F, M, C);
    } else {
        localInlet = gLocalInletMap_cas[&F];
    }


    B.CreateCall(localInlet, {SendResult, Work});
    B.CreateRetVoid();

    B.SetInsertPoint(BBremoteInlet);

    Function * RemoteInlet = nullptr;
    if(gRemoteInletMap_cas.count(&F) == 0){
        RemoteInlet  = GenerateRemoteInlet(F, M, C);
    } else {
        RemoteInlet = gRemoteInletMap_cas[&F];
    }



    Value *WorkSrc = LoadSTyField(B, DL, WorkType::get(C), Work, WorkType::src);
    Value *Zero = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
    Value *InletPtr = B.CreateBitCast(RemoteInlet, VoidPtrTy);
    
    // threadId need to be thread_local
    Constant *threadIdGlobal = M->getOrInsertGlobal("threadId", Int32Ty);
    assert(threadIdGlobal);
    GlobalVariable *gVar = M->getNamedGlobal("threadId");
    gVar->setThreadLocal(true);

    Value *threadId = B.CreateLoad(gVar, "threadId");

    Function *UliSend = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_send);

    B.CreateCall(UliSend, {WorkSrc, Zero, InletPtr, SendResult, SendWork, threadId});
    B.CreateRetVoid();
    
    return Wrapper;

}

void CASABI::BuildSuspendAndStealRoutine (/*input*/CallInst * callInst, Value * returnFromSteal, Value* returnFromSuspend, Function *F, Module *M, LLVMContext & C, /*ouput*/SmallVector<BasicBlock*, 2> &newBB, SmallVector<Instruction*, 2> &delInstrs){
    
    Constant *PRSC_CREATE_WORK = M->getOrInsertFunction("PRSC_CREATE_WORK", WorkType::get(C)->getPointerTo(), WorkType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C), IntegerType::getInt32Ty(C), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), SyncType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C)); 

    IRBuilder<> B(callInst);
    SmallVector<Value*, 8> Args;                                        
    Type * Int32Ty = IntegerType::getInt32Ty(C);
    Type * VoidPtrTy = TypeBuilder<void*, false>::get(C);

    Value *Zero = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
    Value *One = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);                    
    Value *N_One = ConstantInt::get(Int32Ty, -1, /*isSigned=*/true);
    
    Function * callFunc = callInst->getCalledFunction();
    if(gWrapperMap_cas.count(callFunc) == 0){
        // Create the function
        gWrapperMap_cas[callFunc] = GenerateWrapperFunc(*callFunc, M, C);       
    } 
    
    Value * WrapperPtr = B.CreateBitCast(gWrapperMap_cas.lookup(callFunc), VoidPtrTy);  
    
    if(gRecvWorkHandlerMap_cas.count(callFunc) == 0){
        // Create the function
        gRecvWorkHandlerMap_cas[callFunc] = GenerateHereIsWorkHandlerFunc(*callFunc, M, C);       
    } 

    Value *WorkReplyHandlerPtr = B.CreateBitCast(gRecvWorkHandlerMap_cas.lookup(callFunc), VoidPtrTy);
    
    Args.push_back(WorkReplyHandlerPtr); // Handler
    
    Args.push_back(gWork_cas); //  Work pointer
    Args.push_back(WrapperPtr); // Function wrapper


    int nargc=0;
    // Functions argument
    for (User::op_iterator it = callInst->arg_begin(); it != callInst->arg_end(); it++){
        Args.push_back(it->get());
        nargc++;
    }

    StoreInst * storeAfterCall = dyn_cast<StoreInst>(callInst->getNextNode() );
    if( ! (storeAfterCall && gStInstArr_cas[detachLevel_cas] ) ){                    
        storeAfterCall = nullptr;                        
    }
   
    Value *Argc = ConstantInt::get(Int32Ty, nargc, /*isSigned=*/false);

    // Basic Block to resume after all child have return
    BlockAddress* bA = BlockAddress::get(gSyncResumeBB_cas[syncLevel_cas-1]);
    Args.push_back(bA);
    // SP
    Value * pSeedSP  = B.CreateStructGEP(SeedType::get(C), gSeedLocalVar_cas, (unsigned)SeedType::sp);    
    Value * seedSP = B.CreateLoad(IntegerType::getInt8Ty(C)->getPointerTo(), pSeedSP);
    Args.push_back(seedSP);
    // Sync
    Value * PRSCSync  = B.CreateStructGEP(PRSC_DescType::get(C), gPrscDescLocalVar_cas, (unsigned)PRSC_DescType::sync);    
    Args.push_back(PRSCSync);

    Value * res = storeAfterCall? storeAfterCall->getPointerOperand() : 
        ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
                    
    res = B.CreateBitCast(res, VoidPtrTy);

    Args.push_back(res);
                
    Value * ifSuspendTrue = B.CreateICmpEQ(gIsSuspend_cas, One );
    BasicBlock * suspendRoutine = BasicBlock::Create(C, "SuspendRoutine", F);
    BasicBlock * stealRoutine = BasicBlock::Create(C, "StealRoutine", F);
    newBB.push_back(suspendRoutine);
    newBB.push_back(stealRoutine);

                
    B.CreateCondBr(ifSuspendTrue, suspendRoutine, stealRoutine);
    B.SetInsertPoint(suspendRoutine);    
                
    Value * potentialWork = B.CreateCall(PRSC_CREATE_WORK, {gWork_cas, WrapperPtr, Argc, N_One, bA, seedSP, PRSCSync, res, Zero});
    StoreArgIntoWork(C, B, callInst, 0, potentialWork, nargc);

    Constant * PRSC_PUSHFRONT_WORKQ = Get_PRSC_PUSHFRONT_WORKQ(*M);
    B.CreateCall(PRSC_PUSHFRONT_WORKQ, potentialWork);
                
    Constant *PRSC_RESUME_TO_HANDLER = Get_PRSC_RESUME_TO_HANDLER(*M);
    B.CreateCall(PRSC_RESUME_TO_HANDLER, returnFromSuspend);
                                
    B.CreateUnreachable();

    B.SetInsertPoint(stealRoutine);
        
    Function *UliReply = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_reply);
    B.CreateCall(UliReply, Args);

    B.CreateCall(PRSC_RESUME_TO_HANDLER, returnFromSteal);
                                
    B.CreateUnreachable();
        
    if(storeAfterCall){
        delInstrs.push_back(callInst->getNextNode());
    }
    delInstrs.push_back(callInst);
}

void CASABI::StoreArgIntoWork(LLVMContext &C, IRBuilder<> & B, Value * Arg, int offset, Value * potentialWork, int nargc){
    Value * pargv  = B.CreateStructGEP(WorkType::get(C), potentialWork, (unsigned)WorkType::argv);    
    Value * argv = B.CreateLoad(IntegerType::getInt64Ty(C)->getPointerTo(), pargv);
    Value * argvInt = B.CreateCast(Instruction::PtrToInt, argv, IntegerType::getInt64Ty(C));

    // Set w->argv = w->argv-number of arguments
    Value * Narg = ConstantInt::get(IntegerType::getInt64Ty(C), nargc*8, /*isSigned=*/false);        
    Value * argvIntSub  = B.CreateSub(argvInt, Narg);
    argv = B.CreateCast(Instruction::IntToPtr, argvIntSub, IntegerType::getInt8Ty(C)->getPointerTo());
    argv =  B.CreateBitCast(argv, IntegerType::getInt64Ty(C)->getPointerTo());    
    B.CreateStore(argv, pargv);

    for(int ii = 0; ii<nargc; ii++){
        CallInst * callInst = nullptr;
        Function * F = nullptr;
        Value * v = nullptr;
        if (callInst = dyn_cast<CallInst>(Arg)) {
            v = (callInst->arg_begin()+ offset+ii)->get();
        } else if (F = dyn_cast<Function>(Arg)){
            v = F->arg_begin() + offset + ii;
        }

        // Check type
        assert(v);
        if(v->getType()->isIntegerTy()){
            Value * pargv  = B.CreateStructGEP(WorkType::get(C), potentialWork, (unsigned)WorkType::argv);    
            Value * argv = B.CreateLoad(IntegerType::getInt64Ty(C)->getPointerTo(), pargv);           
            Value * storeArg = B.CreateInBoundsGEP(IntegerType::getInt64Ty(C), argv, ConstantInt::get(IntegerType::getInt32Ty(C), ii, /*isSigned=*/false) );
            Value * zext = B.CreateZExt(v, IntegerType::getInt64Ty(C), "t5");
            B.CreateStore(zext, storeArg);
        } else if (v->getType()->isPointerTy()){ 
            Value * pargv  = B.CreateStructGEP(WorkType::get(C), potentialWork, (unsigned)WorkType::argv);    
            Value * argv = B.CreateLoad(IntegerType::getInt64Ty(C)->getPointerTo(), pargv);           
            Value * storeArg = B.CreateInBoundsGEP( IntegerType::getInt64Ty(C), argv, ConstantInt::get(IntegerType::getInt32Ty(C), ii, /*isSigned=*/false) );           
            Value * zext = B.CreateCast(Instruction::PtrToInt, v, IntegerType::getInt64Ty(C));
            B.CreateStore(zext, storeArg);
        } else {
            assert(false && "Type not yet supported");
        }              
    }
} 


Function *CASABI::createDetach(DetachInst &Detach,
                        ValueToValueMapTy &DetachCtxToStackFrame,
                        DominatorTree &DT, AssumptionCache &AC) {
    

    BasicBlock * curBB = Detach.getParent();
    Function * F = curBB->getParent();
    Module * M = F->getParent();
    LLVMContext& C = M->getContext();
    
    BasicBlock * bb = nullptr;
    Instruction * term = nullptr;
    
    // Build type
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);

    // Potential Jump
    Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);

    Detach.dump();
    DetachInst* detachClone = dyn_cast<DetachInst>(VMap[&Detach]);
    
    if(detachClone)
        detachClone->dump();
    
    {
        // Create the Fast Path
        //-------------------------------------------------------------------
        // Add the prologue at beginning of the deattach block

        SmallVector<BasicBlock*, 8> bbList;
        DenseMap<BasicBlock *, bool> haveVisited;

        BasicBlock * detachBB = Detach.getDetached();        
        BasicBlock * continueBB = Detach.getContinue();
        Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);
        Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);
        Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  
        Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  

        BasicBlock   * startOfStealHandler = NULL;
        ReattachInst * prevReattachInst = NULL;

        IRBuilder<> fastBuilder(detachBB->getFirstNonPHIOrDbgOrLifetime()); 
        

        bbList.push_back(detachBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator() ))  ){
                // Don't push anymore if we encountered reattach instruction
                prevReattachInst = dyn_cast<ReattachInst>( bb->getTerminator() );
                startOfStealHandler = prevReattachInst->getDetachContinue();
                fastBuilder.SetInsertPoint( startOfStealHandler->getFirstNonPHIOrDbgOrLifetime() );
                fastBuilder.CreateCall(enauli, {NEG_ZERO});
            } else {
                for( pred_iterator PI = pred_begin(bb); PI!=pred_end(bb); PI++ ){                
                    bbList.push_back(*PI);
                }
            }
        }
        
        // Look for the forkable function. 
        if(prevReattachInst){
            BasicBlock * prevReattachBB = prevReattachInst->getParent();
            for( Instruction &II : *prevReattachBB){
                if(isa<CallInst>(&II)){
                    BasicBlock * stealhandler = dyn_cast<BasicBlock>(VMap[startOfStealHandler]);
                    
                    // Associate callsite instruction with steal handler
                    M->CallStealMap[&II] = stealhandler;
                    // Indicate the steal hander basic block needs a label
                    M->StealHandlerExists[stealhandler] = true;

                    outs() << __FILE__ " " << __func__ << " " << __LINE__ << "\n";
                    II.dump();
                    outs() << "Stealhandler :  " << &II << " "  << M->CallStealMap[&II]->getName()<<"\n";
                    
                    //fastBuilder.SetInsertPoint( &II );
                    //fastBuilder.CreateCall(potentialJump, {BlockAddress::get(stealhandler)});
                                        
                    dyn_cast<CallInst>(&II)->getCalledFunction()->addFnAttr(Attribute::Forkable);
                    break;
                }
            }            
        }

        bbList.clear();
        // Look for the reattach inst
        // Add an epilogue just before it
        bbList.push_back(detachBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator() ))  ){
                // Don't push anynore if we encountered reattach instruction
                fastBuilder.SetInsertPoint(bb->getTerminator());
                fastBuilder.CreateCall(disuli, {ZERO});
            } else {
                for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
                    bbList.push_back(*SI);
                }
            }
        }



    }
    // Create the Slow path
    //-------------------------------------------------------------------
    {

        // clone of DetachBB will become the steal request handler

        SmallVector<BasicBlock*, 8> bbList;
        DenseMap<BasicBlock *, bool> haveVisited;

   
        BasicBlock * detachBB = detachClone->getDetached();        
        BasicBlock * continueBB = detachClone->getContinue();
        Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);
        Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);
        Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  
        Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  

        BasicBlock   * startOfStealHandler= NULL;
        ReattachInst * prevReattachInst = NULL;

        IRBuilder<> slowBuilder(detachBB->getFirstNonPHIOrDbgOrLifetime()); 
        
        bbList.push_back(detachBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator() ))  ){
                // Don't push anymore if we encountered reattach instruction
                prevReattachInst = dyn_cast<ReattachInst>( bb->getTerminator() );
                startOfStealHandler = prevReattachInst->getDetachContinue();
                slowBuilder.SetInsertPoint( startOfStealHandler->getFirstNonPHIOrDbgOrLifetime() );
                slowBuilder.CreateCall(enauli, {NEG_ZERO});
            } else {
                for( pred_iterator PI = pred_begin(bb); PI!=pred_end(bb); PI++ ){                
                    bbList.push_back(*PI);
                }
            }
        }
        
        bbList.clear();

        // Look for the reattach inst
        // Add an epilogue just before it
        bbList.push_back(detachBB);
        while(!bbList.empty()){
            bb = bbList.back();
            bbList.pop_back();
            if ( (haveVisited.lookup(bb)) ){
                continue;
            }
            haveVisited[bb] = true;
            if ( (term = dyn_cast<ReattachInst>( bb->getTerminator() ))  ){
                // Don't push anynore if we encountered reattach instruction
                slowBuilder.SetInsertPoint(bb->getTerminator());
                slowBuilder.CreateCall(disuli, {ZERO});
            } else {
                for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
                    bbList.push_back(*SI);
                }
            }
        }        
    }
    //-------------------------------------------------------------------

    return NULL;
}


void CASABI::preProcessFunction(Function &F) {

  // Add Thread initialization and deinitialization on the main function
  // TODO : Make this optional
  if ( F.getName() == "main") {
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(F.getContext());
    Constant * PRSC_INIT_RT = Get_PRSC_INIT_RT(*F.getParent());
    Constant * PRSC_DEINIT_RT = Get_PRSC_DEINIT_RT(*F.getParent());
    Constant * PRSC_SHOW_STATS = Get_PRSC_SHOW_STATS(*F.getParent());
    
    IRBuilder<> B(F.getEntryBlock().getTerminator());
    B.CreateCall(PRSC_INIT_RT);
    
    for (auto &BB : F){
      Instruction * termInst = BB.getTerminator();
      if(isa<ReturnInst>(termInst)){
          B.SetInsertPoint(termInst);
          B.CreateCall(PRSC_SHOW_STATS);
          B.CreateCall(PRSC_DEINIT_RT);
      }
    }   

    return;
  } 
  
  Module *M = F.getParent();
  Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
  IRBuilder<> builder( F.getContext()  );

  // Clone the function, create the slow path
  // Clone the basic block
  // -------------------------------------------------------------------------
  DebugInfoFinder DIFinder;      
  //ValueToValueMapTy VMap; 
  DISubprogram *SP = F.getSubprogram();
  if (SP) {
      //assert(!MustCloneSP || ModuleLevelChanges);
      // Add mappings for some DebugInfo nodes that we don't want duplicated
      // even if they're distinct.
      auto &MD = VMap.MD();
      MD[SP->getUnit()].reset(SP->getUnit());
      MD[SP->getType()].reset(SP->getType());
      MD[SP->getFile()].reset(SP->getFile());  
      MD[SP].reset(SP); 
  }

  // Delete the alloca in the cloned entry so that it is not used during remap
  SmallVector<Instruction *,2> delInstrs;
  BasicBlock * entryBB =  dyn_cast<BasicBlock>( &F.getEntryBlock()); 
  Instruction * afterAlloca;
  for(Instruction &II : *entryBB){
      if(isa<AllocaInst>(&II)){
          delInstrs.push_back(&II);
      } else {
          afterAlloca = &II;
          break;
      }
      
  }

  // Split the basic block
  auto afterBB =  entryBB->splitBasicBlock(afterAlloca);    
  
  // Collect the basic block to clone
  SmallVector<BasicBlock*, 8> bbV2Clone;
  for( auto &BB : F){
      // Do not clone the alloca instruction
      if(&BB == entryBB)continue;

      bbV2Clone.push_back(&BB);
  }
  
  // Perform the actual cloning
  for (auto pBB : bbV2Clone){
      BasicBlock *bbC = CloneBasicBlock(pBB, VMap, ".clone", &F, nullptr, &DIFinder);
      VMap[pBB] = bbC;        
     
      if(pBB == afterBB){
          builder.SetInsertPoint(entryBB->getTerminator());
          builder.CreateCall(potentialJump, {BlockAddress::get(bbC)});
      }

  }
   
  // --------------------------------------------------------------
  // Remap the cloned instruction
  for (auto pBB : bbV2Clone){
      BasicBlock* bbC = dyn_cast<BasicBlock>(VMap[pBB]);
      for (Instruction &II : *bbC) {
          RemapInstruction(&II, VMap,
                           RF_IgnoreMissingLocals,
                           nullptr, nullptr);
      }
  }



  return;
}

void CASABI::postProcessFunction(Function &F) {
    return;
}

void CASABI::postProcessHelper(Function &F) {
    //assert(false);
}

bool CASABILoopSpawning::processLoop() {
    //assert(false);
  return false;
}

CASABI::CASABI() {}

