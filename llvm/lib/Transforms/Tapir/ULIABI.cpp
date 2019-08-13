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

using namespace llvm;

#define DEBUG_TYPE "uliabi"

using Sync = ULIABI::Sync;
using Work = ULIABI::Work;

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

void ULIABI::createSync(SyncInst &inst, ValueToValueMapTy &DetachCtxToStackFrame) {
  assert(false);
}

Function *ULIABI::createDetach(DetachInst &Detach,
                        ValueToValueMapTy &DetachCtxToStackFrame,
                        DominatorTree &DT, AssumptionCache &AC) {
  assert(false);
  return nullptr;
}

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

typedef void* (*FP)(void);
using Scalar = long long int;
using UliArgType = long long int;

// typedef struct {
//     char bEnqResume;
//     uint counter;
//     char seedStolen;
// } Sync;

using TypeBuilderCache = std::map<LLVMContext *, StructType *>;

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

using WorkType = TypeBuilder<Work, false>;


void ULIABI::preProcessFunction(Function &F) {
  if (F.getName() != "fib") return;
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

    Inlet->dump();
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

    Wrapper->dump();
    F.dump();
  }


  assert(false);
}

void ULIABI::postProcessFunction(Function &F) {
  assert(false);
}

void ULIABI::postProcessHelper(Function &F) {
  assert(false);
}

bool ULIABILoopSpawning::processLoop() {
  assert(false);
  return false;
}

ULIABI::ULIABI() {}
