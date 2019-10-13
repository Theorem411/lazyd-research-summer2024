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
StoreInst  * gStInstArr[MAX_LEVEL];

//  Basic block for generating work
BasicBlock * gGenWorkBBArr[MAX_LEVEL];

// Entry point for generating work
BasicBlock * gGenWorkEntryBB;

BasicBlock * gLastFalseBB[MAX_LEVEL];
BasicBlock * gFirstDetachBB[MAX_LEVEL];
BasicBlock * gLastDetachBB[MAX_LEVEL];
BasicBlock * gSyncResumeBB[MAX_LEVEL];

BasicBlock * oldDetachBB = nullptr;
BlockAddress * oldBA = nullptr;

Value * gPrscDescLocalVar;
Value * gSeedLocalVar;

// Check if we should jump to the suspend routine or to steal routine
Value * gIsSuspend;
Value * gWork;

// Store basic block that is taken if the join counter == 0 (Basic block is basically a jump to sync statement
SmallVector<BasicBlock *, 8> gCntEqZeroBBList;
DenseMap<BasicBlock *, int> gBBtoSyncLevel;

// A map that maps a function to the wrapper function and the here is work reply handler
// TODO : Combine the below map into one single map <Function * , ArrayofFunction>
DenseMap<Function *, Function *> gWrapperMap;
DenseMap<Function *, Function *> gRemoteInletMap;
DenseMap<Function *, Function *> gLocalInletMap;
DenseMap<Function *, Function *> gRecvWorkHandlerMap;

// Store the basic block that is executed after the cilk_sync statment
//DenseMap<Function *, BasicBlock *> gSyncBBMap;
BasicBlock * gSyncBBMap[MAX_LEVEL];

using Sync = ULIABI::Sync;
using Work = ULIABI::Work;
using PRSC_Desc = ULIABI::PRSC_Desc;
using Seed = ULIABI::Seed;

unsigned detachLevel = 0;

unsigned syncLevel =0;

unsigned gSlvlI = 0;

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

using PRSC_PUSHFRONT_FREEQ_ty = void (Work *);
DEFAULT_GET_LIB_FUNC(PRSC_PUSHFRONT_FREEQ)

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

Value *ULIABI::lowerGrainsizeCall(CallInst *GrainsizeCall) {
  assert(false);
  return nullptr;
}

void ULIABI::createSync(SyncInst &SI, ValueToValueMapTy &DetachCtxToStackFrame) {    
    if(gSlvlI == 0 ){
        IRBuilder<> B(gLastFalseBB[syncLevel-1]);
        B.CreateUnreachable();
    }

    BasicBlock &BB = *(SI.getParent());
    Function &Fn = *(BB.getParent());
    Module &M = *(Fn.getParent());

    BasicBlock * syncBB = SI.getSuccessor(0);
    // TODO :  sync?sync_region should be the key instead of function since one function can have multiple sync statement 
    //gSyncBBMap[&Fn] = syncBB;
    gSyncBBMap[gSlvlI] = syncBB;
    gSlvlI++;
}

void ULIABI::SetJoinCounter(IRBuilder <> & B, int val, Module * M, LLVMContext & C){
    Type * Int32Ty = TypeBuilder<int32_t, false>::get(C);
    Value *Val = ConstantInt::get(Int32Ty, detachLevel+2, /*isSigned=*/false);
    Value * PRSCpSync  = B.CreateStructGEP(PRSC_DescType::get(C), gPrscDescLocalVar, (unsigned)PRSC_DescType::sync);
    Constant *PRSC_SET_JOIN = Get_PRSC_SET_JOIN(*M);
    B.CreateCall(PRSC_SET_JOIN, {PRSCpSync, Val});
}


void ULIABI::DecrementJoinCounter(IRBuilder <> & gotStolenB, Module * M, LLVMContext & C){
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  
    Value * PRSCpSync  = gotStolenB.CreateStructGEP(PRSC_DescType::get(C), gPrscDescLocalVar, (unsigned)PRSC_DescType::sync);    
    Constant *PRSC_DEC_JOIN = Get_PRSC_DEC_JOIN(*M);
    Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);    
    gotStolenB.CreateCall(disuli, { ZERO });
    gotStolenB.CreateCall(PRSC_DEC_JOIN, PRSCpSync);
    
}

Value* ULIABI::CheckIfJoinCounterZero(IRBuilder <> & gotStolenB, Module * M, LLVMContext & C){
    Type * Int32Ty = TypeBuilder<int32_t, false>::get(C);
    Value * ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);
    Value * PRSCpSync  = gotStolenB.CreateStructGEP(PRSC_DescType::get(C), gPrscDescLocalVar, (unsigned)PRSC_DescType::sync);    
    Constant *PRSC_CHECKIFZERO_RESUME = Get_PRSC_CHECKIFZERO_RESUME(*M);
    Value * checkCounter = gotStolenB.CreateCall(PRSC_CHECKIFZERO_RESUME, PRSCpSync);
    Value * checkCntRes = gotStolenB.CreateICmpEQ(checkCounter, ONE);
    return checkCntRes;

}

void ULIABI::StoreFuncRes(IRBuilder <> & gotStolenB, int detachLevel, LLVMContext & C){
    // TODO: fix this
    if(gStInstArr[detachLevel]){
        // Does not work, need asm
        //gotStolenB.Insert(gStInstArr[detachLevel], gStInstArr[detachLevel]->getName());
        Value * toStoreTo = gStInstArr[detachLevel]->getPointerOperand();

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


void ULIABI::StoreRetInInlet(IRBuilder <> &B, Argument & Result, Argument & WorkPtr, Type* resTy, LLVMContext & C, const DataLayout &DL) {
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


void ULIABI::PopulateAfterCheckCnt(IRBuilder <> &gotStolenB, BasicBlock * parentBB, Value * checkCntRes, DetachInst &Detach, Function * F, Module * M, LLVMContext & C){
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
    gCntEqZeroBBList.push_back(ifCounterZero);
    gBBtoSyncLevel[ifCounterZero] = syncLevel-1;

    gotStolenB.SetInsertPoint(ifCounterNotZero);
    Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
    gotStolenB.CreateCall(potentialJump, {BlockAddress::get(gSyncResumeBB[syncLevel-1])});
    Constant *PRSC_SUSPEND_AND_CHANGERETADDR = Get_PRSC_SUSPEND_AND_CHANGERETADDR(*M);
    //gotStolenB.CreateCall(enauli, { NEG_ZERO });

    // Suspend for now
    
    CallInst * CI = CallInst::Create(PRSC_SUSPEND_AND_CHANGERETADDR, {BlockAddress::get(parentBB)});

    // TODO: Hack?
    CI->setDebugLoc(Detach.getDebugLoc());
    gotStolenB.Insert(CI);    
    gotStolenB.CreateUnreachable();
}

void ULIABI::GenerateInletEntry(IRBuilder<> & B, Argument & Result, Argument & WorkPtr, Type * resTy, Function * Inlet, Module * M, LLVMContext & C, const DataLayout &DL){    
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
    
    //Value *Worksp = LoadSTyField(B, DL, WorkType::get(C), &WorkPtr, WorkType::sp);
    //Value *Workip = LoadSTyField(B, DL, WorkType::get(C), &WorkPtr, WorkType::ip);
    
    //Constant *PRSC_PUSHFRONT_READYQ = Get_PRSC_PUSHFRONT_READYQ(*M);
    //B.CreateCall(PRSC_PUSHFRONT_READYQ, {Worksp, Workip});
    
    Constant *PRSC_PUSHFRONT_CONTQ = Get_PRSC_PUSHFRONT_CONTQ(*M);
    B.CreateCall(PRSC_PUSHFRONT_CONTQ, &WorkPtr);
    

    B.CreateRetVoid();

    //B.CreateBr(ifCounterNotZero);        
    B.SetInsertPoint(ifCounterNotZero);
    
    Constant *PRSC_PUSHFRONT_FREEQ = Get_PRSC_PUSHFRONT_FREEQ(*M);
    B.CreateCall(PRSC_PUSHFRONT_FREEQ, &WorkPtr);

    //Value *WorkArgv = LoadSTyField(B, DL, WorkType::get(C), &WorkPtr, WorkType::argv);
    

    Instruction * retVoid  = B.CreateRetVoid();

    // TODO: Free the memory here 
    //CallInst * freeWork    = dyn_cast<CallInst>(CallInst::CreateFree(&WorkPtr, retVoid));
    //CallInst * freeArgv = dyn_cast<CallInst>(CallInst::CreateFree(WorkArgv, freeWork));
    
    //freeWork->setTailCall(false); freeArgv->setTailCall(false);

    //ifCounterNotZero->dump();

}

Function * ULIABI::GenerateHereIsWorkHandlerFunc(Function & F, Module * M, LLVMContext & C){

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

Function * ULIABI::GenerateRemoteInlet(Function & F, Module * M, LLVMContext & C){
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
    

    gRemoteInletMap[&F] =  RemoteInlet;

    return RemoteInlet;
}

//TODO :
// Free the work and its argument
// free(w); free(w->argv);
Function * ULIABI::GenerateLocalInlet(Function & F, Module * M, LLVMContext & C){
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
    gLocalInletMap[&F] =  localInlet;
    //Inlet->dump();

    return localInlet;
}

Function * ULIABI::GenerateWrapperFunc(Function & F, Module * M, LLVMContext & C){
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
    if(gLocalInletMap.count(&F) == 0){
        localInlet  = GenerateLocalInlet(F, M, C);
    } else {
        localInlet = gLocalInletMap[&F];
    }


    B.CreateCall(localInlet, {SendResult, Work});
    B.CreateRetVoid();

    B.SetInsertPoint(BBremoteInlet);

    Function * RemoteInlet = nullptr;
    if(gRemoteInletMap.count(&F) == 0){
        RemoteInlet  = GenerateRemoteInlet(F, M, C);
    } else {
        RemoteInlet = gRemoteInletMap[&F];
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

void ULIABI::BuildSuspendAndStealRoutine (/*input*/CallInst * callInst, Value * returnFromSteal, Value* returnFromSuspend, Function *F, Module *M, LLVMContext & C, /*ouput*/SmallVector<BasicBlock*, 2> &newBB, SmallVector<Instruction*, 2> &delInstrs){
    
    Constant *PRSC_CREATE_WORK = M->getOrInsertFunction("PRSC_CREATE_WORK", WorkType::get(C)->getPointerTo(), WorkType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C), IntegerType::getInt32Ty(C), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), SyncType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C)); 

    IRBuilder<> B(callInst);
    SmallVector<Value*, 8> Args;                                        
    Type * Int32Ty = IntegerType::getInt32Ty(C);
    Type * VoidPtrTy = TypeBuilder<void*, false>::get(C);

    Value *Zero = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
    Value *One = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);                    
    Value *N_One = ConstantInt::get(Int32Ty, -1, /*isSigned=*/true);
    
    Function * callFunc = callInst->getCalledFunction();
    if(gWrapperMap.count(callFunc) == 0){
        // Create the function
        gWrapperMap[callFunc] = GenerateWrapperFunc(*callFunc, M, C);       
    } 
    
    Value * WrapperPtr = B.CreateBitCast(gWrapperMap.lookup(callFunc), VoidPtrTy);  
    
    if(gRecvWorkHandlerMap.count(callFunc) == 0){
        // Create the function
        gRecvWorkHandlerMap[callFunc] = GenerateHereIsWorkHandlerFunc(*callFunc, M, C);       
    } 

    Value *WorkReplyHandlerPtr = B.CreateBitCast(gRecvWorkHandlerMap.lookup(callFunc), VoidPtrTy);
    
    Args.push_back(WorkReplyHandlerPtr); // Handler
    
    Args.push_back(gWork); //  Work pointer
    Args.push_back(WrapperPtr); // Function wrapper


    int nargc=0;
    // Functions argument
    for (User::op_iterator it = callInst->arg_begin(); it != callInst->arg_end(); it++){
        Args.push_back(it->get());
        nargc++;
    }

    StoreInst * storeAfterCall = dyn_cast<StoreInst>(callInst->getNextNode() );
    if( ! (storeAfterCall && gStInstArr[detachLevel] ) ){                    
        storeAfterCall = nullptr;                        
    }
   
    Value *Argc = ConstantInt::get(Int32Ty, nargc, /*isSigned=*/false);

    // Basic Block to resume after all child have return
    BlockAddress* bA = BlockAddress::get(gSyncResumeBB[syncLevel-1]);
    Args.push_back(bA);
    // SP
    Value * pSeedSP  = B.CreateStructGEP(SeedType::get(C), gSeedLocalVar, (unsigned)SeedType::sp);    
    Value * seedSP = B.CreateLoad(IntegerType::getInt8Ty(C)->getPointerTo(), pSeedSP);
    Args.push_back(seedSP);
    // Sync
    Value * PRSCSync  = B.CreateStructGEP(PRSC_DescType::get(C), gPrscDescLocalVar, (unsigned)PRSC_DescType::sync);    
    Args.push_back(PRSCSync);

    Value * res = storeAfterCall? storeAfterCall->getPointerOperand() : 
        ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
                    
    res = B.CreateBitCast(res, VoidPtrTy);

    Args.push_back(res);
                
    Value * ifSuspendTrue = B.CreateICmpEQ(gIsSuspend, One );
    BasicBlock * suspendRoutine = BasicBlock::Create(C, "SuspendRoutine", F);
    BasicBlock * stealRoutine = BasicBlock::Create(C, "StealRoutine", F);
    newBB.push_back(suspendRoutine);
    newBB.push_back(stealRoutine);

                
    B.CreateCondBr(ifSuspendTrue, suspendRoutine, stealRoutine);
    B.SetInsertPoint(suspendRoutine);    
                
    Value * potentialWork = B.CreateCall(PRSC_CREATE_WORK, {gWork, WrapperPtr, Argc, N_One, bA, seedSP, PRSCSync, res, Zero});
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

void ULIABI::StoreArgIntoWork(LLVMContext &C, IRBuilder<> & B, Value * Arg, int offset, Value * potentialWork, int nargc){
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


Function *ULIABI::createDetach(DetachInst &Detach,
                        ValueToValueMapTy &DetachCtxToStackFrame,
                        DominatorTree &DT, AssumptionCache &AC) {

    BasicBlock * curBB = Detach.getParent();
    Function * F = curBB->getParent();
    Module * M = F->getParent();
    LLVMContext& C = M->getContext();
    BasicBlock * detachBB = Detach.getDetached();        
    BasicBlock * continueBB = Detach.getContinue();
    const DataLayout &DL = M->getDataLayout();
        
    // Create the work Generation
    SmallVector<BasicBlock*, 8> bbV2Clone;
    SmallVector<BasicBlock*, 8> bbList;
    SmallVector<Instruction *,2> delInstrs;
    DenseMap<BasicBlock *, bool> haveVisited;

    ValueToValueMapTy VMap;    
    BasicBlock * bb = nullptr;
    Instruction * term = nullptr;
      
    // Build type
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);
        
    static IRBuilder<> workFSMB(gGenWorkEntryBB);
  
    // Search for basic block to clone : Look for the next cilk_spawn or sync instruction
    bbList.push_back(continueBB);
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
            // Don't push anynore if we encountered reattach instruction
            bbV2Clone.push_back(bb);
        } else if ( (term = dyn_cast<SyncInst>(bb->getTerminator())) ){
            // Don't push anynore if we encountered sync instruction
            bbV2Clone.push_back(bb);
            
            // Sync Resume
            {
                gSyncResumeBB[syncLevel] = BasicBlock::Create(C, "syncResume", F);
                IRBuilder <> B(gSyncResumeBB[syncLevel]);
                //B.SetInsertPoint(gSyncResumeBB[syncLevel]); 
                B.CreateUnreachable();
            }

            if(syncLevel == 0){
                workFSMB.SetInsertPoint(gGenWorkEntryBB);
            }

            // Reset detachLevel and update SyncLevel
            detachLevel = 0;
            oldDetachBB = nullptr;
            oldBA = nullptr;
            memset(gGenWorkBBArr, 0, MAX_LEVEL*sizeof(BasicBlock*));
            syncLevel++;

        } else {
            bbV2Clone.push_back(bb);
            for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
                bbList.push_back(*SI);
            }
        }
    }
    
    // Look for potential Store operation
    StoreInst * potentialSt = dyn_cast<StoreInst>(detachBB->getFirstNonPHIOrDbgOrLifetime()->getNextNode() );
    if(potentialSt){                    
        // Get the IR to store
        Value *arg0 = potentialSt->getOperand(0);
        Instruction * callInst = detachBB->getFirstNonPHIOrDbgOrLifetime();
        // Check if it is the same with the call instruction
        if( !arg0->getName().compare(callInst->getName()) ){
            gStInstArr[detachLevel] = potentialSt;                        
        } 
    }
    
    // Used for pushing and popping seeds
    if(detachLevel==0){
        gLastDetachBB[syncLevel-1] = detachBB;
    }
    gFirstDetachBB[syncLevel-1] =   curBB;



    // Clone the basic block
    // -------------------------------------------------------------------------
    DebugInfoFinder DIFinder;      
    DISubprogram *SP = F->getSubprogram();
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

    for(auto BB : bbV2Clone){
        BasicBlock *bbC = CloneBasicBlock(BB, VMap, ".workGen_Steal", F, nullptr,
                                          &DIFinder);
        VMap[BB] = bbC;            
    }
    // -------------------------------------------------------------------------
   
    gGenWorkBBArr[detachLevel] = dyn_cast<BasicBlock>(VMap[continueBB]);

    Instruction * potentialCall = nullptr;
    bool bFoundPotentialCall = false;
        
    for(auto BB : bbV2Clone){
        SmallVector<BasicBlock*, 2> newBB;
        BasicBlock *CBB = dyn_cast<BasicBlock>(VMap[BB]);

        Instruction *iterm  = CBB->getTerminator();
                    
        if(DetachInst * itermDet = dyn_cast<DetachInst>(iterm)){
            // Replace detach instruction with branch instruction
            BasicBlock * detachBB = itermDet->getDetached();
            BranchInst *detachBr = BranchInst::Create(detachBB);
            ReplaceInstWithInst(itermDet, detachBr);

              
        } else if(ReattachInst * itermRet = dyn_cast<ReattachInst>(iterm)){
            // Replace the basic block with set of instruction to create/send work
            Instruction * instr = CBB->getFirstNonPHIOrDbgOrLifetime();
            CallInst * callInst = dyn_cast<CallInst>(instr);
            assert(callInst && "First instruction not a call instruction. Seems like something is wrong");
            Value *Zero = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
            Value *One = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);                                   
            BuildSuspendAndStealRoutine(callInst, Zero, One, F, M, C, newBB, delInstrs);                     
            delInstrs.push_back(iterm);
        } else {
            // Look for potential parallel call function that does not have cilk_spawn that precedes it
            for(Instruction &I : *CBB){
                if(CallInst * callInst = dyn_cast<CallInst>(&I)){
                    DEBUG(dbgs() << "Instruction to send\n");                            
                    potentialCall = &I;
                    bFoundPotentialCall = true;
                }
            }
        }

        if ( SyncInst * itermSync = dyn_cast<SyncInst>(iterm) ) {
            if(bFoundPotentialCall){
                // Replace the basic block with set of instruction to create/send work inside the sync 
                CallInst * callInst = dyn_cast<CallInst>(potentialCall);
                Value *Two = ConstantInt::get(Int32Ty, 2, /*isSigned=*/false);
                Value *Three = ConstantInt::get(Int32Ty, 3, /*isSigned=*/false);

                BuildSuspendAndStealRoutine(callInst, Two, Three, F, M, C, newBB, delInstrs);                     
                delInstrs.push_back(iterm);
            }
        }
              
            
        // Remap instruction
        for (Instruction &II : *CBB) {
            RemapInstruction(&II, VMap,
                             RF_IgnoreMissingLocals,
                             nullptr, nullptr);
        }

        // New basic blocks also needs remap
        for(auto newBB_elem : newBB){
            for (Instruction &II : *newBB_elem){
                RemapInstruction(&II, VMap,
                                 RF_IgnoreMissingLocals,
                                 nullptr, nullptr);
            }
        }                  
    }        

     for (auto In : delInstrs){
        Instruction& inst = *In;
        inst.eraseFromParent(); // delete instrs
    }


    //==========================================================================
    // Got stolen case
    BasicBlock * gotStolenArr[MAX_LEVEL];
    gotStolenArr[0] = BasicBlock::Create(C, "gotStolen", F);
    IRBuilder<> gotStolenB (gotStolenArr[0]);
    int tmpLevel = detachLevel;
    
    StoreFuncRes(gotStolenB, detachLevel, C);
    DecrementJoinCounter(gotStolenB, M, C);
    Value * checkCntRes = CheckIfJoinCounterZero(gotStolenB, M, C);    
    PopulateAfterCheckCnt(gotStolenB, gotStolenArr[0], checkCntRes, Detach, F, M, C);
    
    while(tmpLevel > 0){
        gotStolenArr[detachLevel-tmpLevel+1] = BasicBlock::Create(C, "gotStolen", F);         
        gotStolenB.SetInsertPoint(gotStolenArr[detachLevel-tmpLevel+1]);
        
        StoreFuncRes(gotStolenB, detachLevel, C);
        DecrementJoinCounter(gotStolenB, M, C);
        Value * checkCntRes = CheckIfJoinCounterZero(gotStolenB, M, C);    
        PopulateAfterCheckCnt(gotStolenB, gotStolenArr[detachLevel-tmpLevel+1], checkCntRes, Detach, F, M, C);

        tmpLevel--;
    }

    // 
    
    //==========================================================================
    // gGenWorkEntryBB
    // Create FSM for choosing which work to send

    // Load the return Address
    Value * PRSCSP  = workFSMB.CreateStructGEP(SeedType::get(C), gSeedLocalVar, (unsigned)SeedType::sp);    
    Value * Eight = ConstantInt::get(Int64Ty, 8, /*isSigned=*/false);
    Value * SPVal = workFSMB.CreateLoad(IntegerType::getInt8Ty(C)->getPointerTo(), PRSCSP);
    Value * SPValInt = workFSMB.CreateCast(Instruction::PtrToInt, SPVal, IntegerType::getInt64Ty(C));
    Value * ppRA  = workFSMB.CreateSub(SPValInt, Eight);
    ppRA = workFSMB.CreateCast(Instruction::IntToPtr, ppRA, IntegerType::getInt8Ty(C)->getPointerTo());
    ppRA =  workFSMB.CreateBitCast(ppRA, ppRA->getType()->getPointerTo());
    Value * pRA = workFSMB.CreateLoad(IntegerType::getInt8Ty(C)->getPointerTo(), ppRA);


    BasicBlock * ifTrue = BasicBlock::Create(C, "TrueBB", F);
    BasicBlock * ifFalse = BasicBlock::Create(C, "FalseBB", F);

    BlockAddress* bA = BlockAddress::get(detachBB);   
    Value * cmpRes = workFSMB.CreateICmpUGE(pRA,bA);

    BlockAddress* bA2 = BlockAddress::get(continueBB);   
    Value * cmpRes2 = workFSMB.CreateICmpULE(pRA, bA2);

    cmpRes = workFSMB.CreateAnd(cmpRes, cmpRes2);

    workFSMB.CreateCondBr(cmpRes, ifTrue, ifFalse);
    workFSMB.SetInsertPoint(ifTrue);

    SetJoinCounter(workFSMB, detachLevel+2, M, C);

    bA = BlockAddress::get(gotStolenArr[0]);
    workFSMB.CreateStore(bA, ppRA);
    
    Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
    
    //TODO : Fix this. Hack
    workFSMB.CreateCall(potentialJump, {bA});


    if(oldDetachBB){
        //TODO : Fix this. Hack 
        BasicBlock * cloneOldDetachBB = dyn_cast<BasicBlock>(VMap[oldDetachBB]);
        IRBuilder <> detachB (cloneOldDetachBB->getTerminator());
        detachB.CreateCall(potentialJump, {oldBA});
        detachB.CreateCall(potentialJump, {bA});
    }

    oldBA = bA;

    if(gGenWorkBBArr[detachLevel])
        workFSMB.CreateBr(gGenWorkBBArr[detachLevel]);

    workFSMB.SetInsertPoint(ifFalse);
    gLastFalseBB[syncLevel-1] = ifFalse;

    tmpLevel = detachLevel;
    while(tmpLevel > 0){
        //assert(false && "Not working yet, code needs update");
        bA = BlockAddress::get(gotStolenArr[detachLevel-tmpLevel]);        
        ifTrue = BasicBlock::Create(C, "TrueBB", F);
        ifFalse = BasicBlock::Create(C, "FalseBB", F);
        
        Value * cmpRes = workFSMB.CreateICmpEQ(pRA,bA);
        workFSMB.CreateCondBr(cmpRes, ifTrue, ifFalse);
           
        workFSMB.SetInsertPoint(ifTrue);
        
        if(gotStolenArr[detachLevel-tmpLevel+1]){
            bA = BlockAddress::get(gotStolenArr[detachLevel-tmpLevel+1]);
            workFSMB.CreateStore(bA, ppRA);
            
            IRBuilder <> detachB(gotStolenArr[detachLevel-tmpLevel]->getTerminator());        
            //detachB.SetInsertPoint(gotStolenArr[detachLevel-tmpLevel]->getTerminator());        
            detachB.CreateCall(potentialJump, {bA});

        }

        if(gGenWorkBBArr[tmpLevel-1])          
            workFSMB.CreateBr(gGenWorkBBArr[tmpLevel-1]);
        
        workFSMB.SetInsertPoint(ifFalse);
        gLastFalseBB[syncLevel-1] = ifFalse;

        tmpLevel--;
    }   
    
    //gGenWorkEntryBB->dump();
   detachLevel++;
   oldDetachBB = detachBB;
   //F->dump();
   return nullptr;
}


void ULIABI::preProcessFunction(Function &F) {
  if ( F.getName() == "main") {
    F.addFnAttr(Attribute::ULINoPolling);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(F.getContext());
    Constant * PRSC_INIT_RT = Get_PRSC_INIT_RT(*F.getParent());
    Constant * PRSC_DEINIT_RT = Get_PRSC_DEINIT_RT(*F.getParent());
    Constant * PRSC_SHOW_STATS = Get_PRSC_SHOW_STATS(*F.getParent());
    
    IRBuilder<> B(F.getEntryBlock().getTerminator());
    B.CreateCall(PRSC_INIT_RT);
    
    //B.SetInsertPoint(F.getTerminator());
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
  

  // Initialize global variable
  detachLevel = 0;
  syncLevel = 0;
  gSlvlI = 0;
  gCntEqZeroBBList.clear();
  //gWrapperMap.clear();
  //gRemoteInletMap.clear();
  //gLocalInletMap.clear();
  //gRecvWorkHandlerMap.clear();
  //gSyncBBMap.clear();
  gBBtoSyncLevel.clear();  
  gGenWorkEntryBB = nullptr;

  llvm::errs() << "preprocessing " << F.getName() << "...\n";

  // Make it non inlinable
  F.addFnAttr(Attribute::NoInline);

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
  //assert(RetType == Int32Ty || RetType == Int64Ty);

  Type *WorkPtrTy = TypeBuilder<Work*, false>::get(C);
  
  BasicBlock & entry  = F.getEntryBlock();
  IRBuilder<> B(entry.getFirstNonPHIOrDbgOrLifetime());
  
  // Call ENAULI
  Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);
  Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  
  Value *ZERO32 = ConstantInt::get(Int32Ty, 0x0, /*isSigned=*/false);  
  B.CreateCall(enauli, { NEG_ZERO });

  Constant *POLL = Get_POLL(*M);
  B.CreateCall(POLL, { ZERO32 });

  // Allocate PRSC_Desc
  Type *PRSC_DescTy = PRSC_DescType::get(C);
  gPrscDescLocalVar = B.CreateAlloca(PRSC_DescTy, DL.getAllocaAddrSpace(), nullptr, "PRSC_Dec");
  

  // Get all the exit block and put DISULI before return
  for (auto &BB : F){
      Instruction * termInst = BB.getTerminator();
      if(isa<ReturnInst>(termInst)){
          B.SetInsertPoint(termInst);
          Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);
          Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  
          B.CreateCall(disuli, { ZERO });
      }
  }

#if 0  
  Function *RemoteInlet = nullptr;
  // Remote Inlet
  {
    FunctionType *InletTy = FunctionType::get(VoidTy, {Int32Ty, UliArgTypeTy, WorkPtrTy, Int32Ty}, /*isVarArg=*/false);
    auto Name = "__prsc_" + F.getName() + "Remote_Inlet";
    RemoteInlet = Function::Create(InletTy, InternalLinkage, Name, M);
    RemoteInlet->addFnAttr(Attribute::UserLevelInterrupt);
    RemoteInlet->setCallingConv(CallingConv::X86_ULI);
    BasicBlock *Entry = BasicBlock::Create(C, "entry", RemoteInlet);
    IRBuilder<> B(Entry);
    

    Argument &FromArg = RemoteInlet->arg_begin()[0];
    Argument &Result = RemoteInlet->arg_begin()[1];
    Argument &WorkPtr = RemoteInlet->arg_begin()[2];
    Argument &From2Arg = RemoteInlet->arg_begin()[3];
     
    // TODO: assert equal?
    // Value *FromMatch = B.CreateICmpEQ(&FromArg, &From2Arg);
    
    GenerateInletEntry(B, Result, WorkPtr, RetType, RemoteInlet, M, C, DL);    
    gRemoteInletMap[&F] =  RemoteInlet;
   
  }

  // Local inlet
  Function * localInlet = nullptr;
  {
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
    

    gLocalInletMap[&F] =  localInlet;
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

    B.CreateCall(localInlet, {SendResult, Work});
    B.CreateRetVoid();

    B.SetInsertPoint(BBremoteInlet);

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
    
    // Store the wrapper function
    gWrapperMap[&F] =  Wrapper;
  }
#endif

  
  // Work Generation
  {
    B.SetInsertPoint(F.getEntryBlock().getTerminator());
    gSeedLocalVar = B.CreateAlloca(SeedType::get(C), DL.getAllocaAddrSpace(), nullptr, "seed");
    gGenWorkEntryBB = BasicBlock::Create(C, "seedGen", &F);


    B.SetInsertPoint(gGenWorkEntryBB);

    // Fix the rbp first using the rsp
    Function *SetupRBPfromRSPinRBP = Intrinsic::getDeclaration(M, Intrinsic::x86_setup_rbp_from_sp_in_rbp);
    B.CreateCall(SetupRBPfromRSPinRBP);

    //==========================================================================
    // Create Prologue for gGenWorkEntryBB
    using AsmPrototype = int (void);
    using AsmPrototypeLong = long (void);
    FunctionType *FAsmTy =
        TypeBuilder<AsmPrototype, false>::get(B.getContext());
    FunctionType *FAsmLongTy =
        TypeBuilder<AsmPrototypeLong, false>::get(B.getContext());

    // Get the type of routine
    Value *Asm = InlineAsm::get(FAsmTy,
                              "movl 0(%rsp), $0\0A\09",
                              "=r,~{dirflag},~{fpsr},~{flags}",
                              /*sideeffects*/ true);
    gIsSuspend = B.CreateCall(Asm);

    Value * Asm2 = InlineAsm::get(FAsmLongTy, 
                         "movq -8(%rsp), $0\0A\09",
                         "=r,~{dirflag},~{fpsr},~{flags}",
                         /*sideeffects*/ true);

    gWork = B.CreateCall(Asm2);

    gWork->getType()->dump();
    gWork = B.CreateCast(Instruction::IntToPtr, gWork, IntegerType::getInt8Ty(C)->getPointerTo());
    gWork->getType()->dump();

    gWork = B.CreateBitCast(gWork, WorkType::get(C)->getPointerTo());    
  }

#if 0  
  // Here is work Handler
  {
   SmallVector<Type *, 8> WorkHandlerParamTys(FTy->param_begin(), FTy->param_end());
   WorkHandlerParamTys.insert(WorkHandlerParamTys.begin(), VoidPtrTy);
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

   Constant *PRSC_RESET_WORKSTEAL = Get_PRSC_RESET_WORKSTEAL(*M);
   B.CreateCall(PRSC_RESET_WORKSTEAL);

   Value * from = HereIsWorkHandler->arg_begin();
   Value * fp = HereIsWorkHandler->arg_begin()+1;   
   Value * res = HereIsWorkHandler->arg_end()-1;
   Value * sync = HereIsWorkHandler->arg_end()-2;
   Value * parentSP = HereIsWorkHandler->arg_end()-3;
   Value * parentIP = HereIsWorkHandler->arg_end()-4;   
   Value * realArgStart = HereIsWorkHandler->arg_begin() + 2;
   
   int numArgs = HereIsWorkHandler->arg_end()-HereIsWorkHandler->arg_begin();
   int realNumArgs = numArgs - 6;// Remove from, fp, res, syn, parentSP/IP

   Value * ARGC =  ConstantInt::get(Int32Ty, realNumArgs, /*isSigned=*/false);
   Value * ONE =  ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);
  
   // Check if fp is NULL
   BasicBlock * fpIsNotNull = BasicBlock::Create(C, "fpIsNotNull", HereIsWorkHandler);
   BasicBlock * fpIsNull = BasicBlock::Create(C, "fpIsNull", HereIsWorkHandler);
   Value * isFpNull = B.CreateICmpEQ(fp, ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo()) );
   
   B.CreateCondBr(isFpNull, fpIsNull, fpIsNotNull);
   B.SetInsertPoint(fpIsNotNull);      

   Constant *PRSC_CREATE_WORK = M->getOrInsertFunction("PRSC_CREATE_WORK", WorkType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C), IntegerType::getInt64Ty(C), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), SyncType::get(C)->getPointerTo(), IntegerType::getInt8Ty(C)->getPointerTo(), IntegerType::getInt32Ty(C)); 

   Value * potentialWork = B.CreateCall(PRSC_CREATE_WORK, {fp, ARGC, from, parentIP, parentSP, sync, res, ONE});

   StoreArgIntoWork(C, B, HereIsWorkHandler, 3, potentialWork, realNumArgs);

   Constant * PRSC_PUSHFRONT_WORKQ = Get_PRSC_PUSHFRONT_WORKQ(*M);
   B.CreateCall(PRSC_PUSHFRONT_WORKQ, potentialWork);

   B.CreateRetVoid();
   
   B.SetInsertPoint(fpIsNull);
   B.CreateRetVoid();
    
   // Store the here is work handler function
   gRecvWorkHandlerMap[&F] =  HereIsWorkHandler;
  }
#endif

}

void ULIABI::postProcessFunction(Function &F) {
    
    LLVMContext &C = F.getContext();
    Module *M = F.getParent();
    const DataLayout &DL = M->getDataLayout();
    Type *Int64Ty = TypeBuilder<int64_t, false>::get(C);
    Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);
    
    // TODO : Handle multiple sync case
    // For pushing and popping the seed 
    //-=======================================================================
    Constant *PRSC_PUSHFRONT_SEEDQ = Get_PRSC_PUSHFRONT_SEEDQ(*M);
    Constant *PRSC_POPFRONT_SEEDQ = Get_PRSC_POPFRONT_SEEDQ(*M);
    Constant *POLL = Get_POLL(*M);
    Function *GetSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);
    
    IRBuilder<> B(gFirstDetachBB[0]->getTerminator());
    Value * currSp = B.CreateCall(GetSP);    
    Value * pSeedSP  = B.CreateStructGEP(SeedType::get(C), gSeedLocalVar, (unsigned)SeedType::sp);    
    currSp = B.CreateCast(Instruction::IntToPtr, currSp, IntegerType::getInt8Ty(C)->getPointerTo());

    Value * seedStoreSp = B.CreateStore(currSp, pSeedSP);
    
    Value * seedIP  = B.CreateStructGEP(SeedType::get(C), gSeedLocalVar, (unsigned)SeedType::ip);    
    BlockAddress* seedGenAddr = BlockAddress::get(gGenWorkEntryBB);

    Function * enauli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_enable);
    Value *NEG_ZERO = ConstantInt::get(Int64Ty, 0xFFFFFFFFFFFFFFFF, /*isSigned=*/false);  

    Function * disuli = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_disable);
    Value *ZERO = ConstantInt::get(Int64Ty, 0, /*isSigned=*/false);  
    Value *ZERO32 = ConstantInt::get(Int32Ty, 0x0, /*isSigned=*/false);  
    
    B.CreateCall(disuli, { ZERO });
    Value * seedStoreIp = B.CreateStore(seedGenAddr, seedIP);
    Value * pSeedLocal = B.CreateBitCast(gSeedLocalVar, SeedType::get(C)->getPointerTo());    
    B.CreateCall(PRSC_PUSHFRONT_SEEDQ, pSeedLocal);
    // Add potential jump
    Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
    B.CreateCall(potentialJump, {BlockAddress::get(gGenWorkEntryBB)});

    for (unsigned i =1; i<syncLevel; i++){
        B.SetInsertPoint(gFirstDetachBB[i]->getTerminator());

        Value * currSp = B.CreateCall(GetSP);    
        Value * pSeedSP  = B.CreateStructGEP(SeedType::get(C), gSeedLocalVar, (unsigned)SeedType::sp);    
        currSp = B.CreateCast(Instruction::IntToPtr, currSp, IntegerType::getInt8Ty(C)->getPointerTo());
        
        Value * seedStoreSp = B.CreateStore(currSp, pSeedSP);
        
        Value * seedIP  = B.CreateStructGEP(SeedType::get(C), gSeedLocalVar, (unsigned)SeedType::ip);    
        BlockAddress* seedGenAddr = BlockAddress::get(gGenWorkEntryBB);

        B.CreateCall(disuli, { ZERO });
        Value * seedStoreIp = B.CreateStore(seedGenAddr, seedIP);
        Value * pSeedLocal = B.CreateBitCast(gSeedLocalVar, SeedType::get(C)->getPointerTo());    
        B.CreateCall(PRSC_PUSHFRONT_SEEDQ, pSeedLocal);
        // Add potential jump
        Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
        B.CreateCall(potentialJump, {BlockAddress::get(gGenWorkEntryBB)});

    }

    for (unsigned i =0; i<syncLevel; i++){
        B.SetInsertPoint(gLastDetachBB[i]->getTerminator());
        B.CreateCall(PRSC_POPFRONT_SEEDQ);
        
        B.CreateCall(enauli, { NEG_ZERO });
        B.CreateCall(POLL, { ZERO32 });
    }
    
    // For the sync resume
    //-======================================================================
    
    for (unsigned i = 0; i<syncLevel; i++){
        B.SetInsertPoint(gSyncResumeBB[i]);    
        Instruction * syncTerm = gSyncResumeBB[i]->getTerminator();
    
        // Fix base pointer
        Function *SetupRBPfromRSP = Intrinsic::getDeclaration(M, Intrinsic::x86_setup_rbp_from_rsp);
        B.CreateCall(SetupRBPfromRSP);

        // Branch to the sync
        B.CreateBr(gSyncBBMap[i]);
    
        // Delete the previous terminator instruction
        syncTerm->eraseFromParent();
    }
    
    // For gotStolen
    //-==================================================================
    // TODO fix this
    for( auto BB : gCntEqZeroBBList ){
        Instruction * term  = BB->getTerminator();
        B.SetInsertPoint(term);

        assert(gBBtoSyncLevel.count(BB) != 0);

        B.CreateBr(gSyncBBMap[gBBtoSyncLevel.lookup(BB)]);
        term->eraseFromParent();
    }

}

void ULIABI::postProcessHelper(Function &F) {
    //assert(false);
}

bool ULIABILoopSpawning::processLoop() {
    //assert(false);
  return false;
}

ULIABI::ULIABI() {}

