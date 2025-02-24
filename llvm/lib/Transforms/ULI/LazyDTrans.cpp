#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/ULI/LazyDTrans.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Local.h"

#include <iostream>

#define DEBUG_TYPE "lazyd-trans"

using namespace llvm;

// Set the size of the work context length
static cl::opt<int> WorkCtxLen(
"lazy-set-workctx-len", cl::init(WORKCTX_SIZE), cl::NotHidden,
  cl::desc("Size of work context length (default=WORKCTX_SIZE)"));

// Set the size of maximum grain size
static cl::opt<int> MaxGrainSize(
"lazy-set-maxgrainsize", cl::init(2048), cl::NotHidden,
  cl::desc("Maximum grain size for parallel for"));

// Set the size of maximum grain size
static cl::opt<int> MaxInstPoll(
"lazy-set-maxinstpoll", cl::init(1), cl::NotHidden,
  cl::desc("Maximum number of instruction to enable poll"));

// Polling at prologue, epilogue, and inner loop
static cl::opt<int> EnableProperPolling(
"lazy-enable-proper-polling", cl::init(0), cl::NotHidden,
  cl::desc("Enable polling at prologue, epilogue, and inner loop (default = 0)"));

// Do not add the polling instrumentation
static cl::opt<bool> DisableUnwindPoll(
"lazy-disable-unwind-polling", cl::init(false), cl::NotHidden,
  cl::desc("Do not insert any polling call (default = off)"));

// Instrument main function
static cl::opt<bool> EnableMainInstrumentation(
"lazy-enable-main-instrumentation", cl::init(true), cl::NotHidden,
  cl::desc("Use to enable main function instrumentation automatically (default = on)"));

// Support only unwinding the same frame once
static cl::opt<bool> EnableUnwindOnce(
"lazy-enable-unwind-once", cl::init(true), cl::NotHidden,
  cl::desc("Enable unwind once for each stack frame (default = on)"));

// Copied from CilkABI.cpp
/// Helper methods for storing to and loading from struct fields.
static Value *GEP(IRBuilder<> &B, Value *Base, int Field) {
  // return B.CreateStructGEP(cast<PointerType>(Base->getType()),
  //                          Base, field);
  return B.CreateConstInBoundsGEP2_32(
      Base->getType()->getScalarType()->getPointerElementType(), Base, 0,
      Field);

}

static unsigned GetAlignment(const DataLayout &DL, StructType *STy, int field) {
  return DL.getPrefTypeAlignment(STy->getElementType(field));
}

static void StoreSTyField(IRBuilder<> &B, const DataLayout &DL, StructType *STy,
                          Value *Val, Value *Dst, int Field,
                          bool isVolatile = false,
                          AtomicOrdering Ordering = AtomicOrdering::NotAtomic) {
  StoreInst *S = B.CreateAlignedStore(Val, GEP(B, Dst, Field),
                                      Align(GetAlignment(DL, STy, Field)), isVolatile);
  S->setOrdering(Ordering);
}

static Value *LoadSTyField(
    IRBuilder<> &B, const DataLayout &DL, StructType *STy, Value *Src,
    int Field, bool isVolatile = false,
    AtomicOrdering Ordering = AtomicOrdering::NotAtomic) {
  Value *GetElPtr = GEP(B, Src, Field);
  LoadInst *L =
      B.CreateAlignedLoad(GetElPtr->getType()->getPointerElementType(),
                          GetElPtr, Align(GetAlignment(DL, STy, Field)), isVolatile);
  L->setOrdering(Ordering);
  return L;
}

#define UNWINDRTS_FUNC(name, M) Get__unwindrts_##name(M)

//using hashGnui_ty = unsigned (unsigned);
static FunctionCallee Get_hashGnui(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("hashGnui", FunctionType::get(Type::getInt32Ty(Ctx), {Type::getInt32Ty(Ctx)}, false));
}

//using push_workctx_ty = void (void**, void*);
static FunctionCallee Get_push_workctx(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("push_workctx", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo(), PointerType::getInt8PtrTy(Ctx)}, false));
}

//using pop_workctx_ty = void (void**, void*);
static FunctionCallee Get_pop_workctx(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("pop_workctx", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo(), PointerType::getInt8PtrTy(Ctx)}, false));
}

//using suspend2scheduler_ty = void (int, int, int);
static FunctionCallee Get_suspend2scheduler(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("suspend2scheduler", FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx),Type::getInt32Ty(Ctx),Type::getInt32Ty(Ctx)}, false));
}

//using resume2scheduler_ty = void (void**, void* );
static FunctionCallee Get_resume2scheduler(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("resume2scheduler", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo(), PointerType::getInt8PtrTy(Ctx)}, false));
}


//using sync_slowpath_ty = char (int, int, void*);
static FunctionCallee Get_sync_slowpath(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("sync_slowpath", FunctionType::get(Type::getInt1Ty(Ctx), {Type::getInt32Ty(Ctx), Type::getInt32Ty(Ctx), PointerType::getInt8PtrTy(Ctx)}, false));
}

//using can_direct_steal_ty = void ();
static FunctionCallee Get_can_direct_steal(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("can_direct_steal", FunctionType::get(Type::getVoidTy(Ctx), {}, false));
}


//using measure_resume_parent_ty = void (int);
static FunctionCallee Get_measure_resume_parent(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("measure_resume_parent", FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx)}, false));
}

//using get_workcontext_ty = void** (void** );
static FunctionCallee Get_get_workcontext(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("get_workcontext", FunctionType::get(PointerType::getInt8PtrTy(Ctx)->getPointerTo(), {PointerType::getInt8PtrTy(Ctx)->getPointerTo()}, false));
}

//using get_workcontext_locowner_ty = void** (int, int, void*);
static FunctionCallee Get_get_workcontext_locowner(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("get_workcontext_locowner", FunctionType::get(PointerType::getInt8PtrTy(Ctx)->getPointerTo(), {Type::getInt32Ty(Ctx), Type::getInt32Ty(Ctx), PointerType::getInt8PtrTy(Ctx)}, false));
}

//using get_stacklet_ctx_ty = void** ();
static FunctionCallee Get_get_stacklet_ctx(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("get_stacklet_ctx", FunctionType::get(PointerType::getInt8PtrTy(Ctx)->getPointerTo(), {}, false));
}

//using initialize_parallel_ctx_ty = void (void**, void*, void*);
static FunctionCallee Get_initialize_parallel_ctx(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("initialize_parallel_ctx", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo(), PointerType::getInt8PtrTy(Ctx), PointerType::getInt8PtrTy(Ctx)}, false));
}

//using initworkers_env_ty = void (void );
static FunctionCallee Get_initworkers_env(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("initworkers_env", FunctionType::get(Type::getVoidTy(Ctx), {}, false));
}


//using deinitworkers_env_ty = void (void );
static FunctionCallee Get_deinitworkers_env(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("deinitworkers_env", FunctionType::get(Type::getVoidTy(Ctx), {}, false));
}


//using deinitperworkers_sync_ty = void(int, int);
static FunctionCallee Get_deinitperworkers_sync(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("deinitperworkers_sync", FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx), Type::getInt32Ty(Ctx)}, false));
}


//using initperworkers_sync_ty = void(int, int);
static FunctionCallee Get_initperworkers_sync(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("initperworkers_sync", FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx), Type::getInt32Ty(Ctx)}, false));
}


// Based on HWAddressSanitizer.cpp
static Value *readRegister(IRBuilder<> &IRB, StringRef Name) {
  Module *M = IRB.GetInsertBlock()->getParent()->getParent();
  LLVMContext *C = &(M->getContext());
  Type * Int64Ty = IRB.getInt64Ty();
  auto *ReadRegister = Intrinsic::getDeclaration(M, Intrinsic::read_register, Int64Ty);
  MDNode *MD = MDNode::get(*C, {MDString::get(*C, Name)});
  Value *Args[] = {MetadataAsValue::get(*C, MD)};
  return IRB.CreateCall(ReadRegister, Args);
}

static Value* getSP(IRBuilder<> &B, Function& F) {
  auto TargetTriple = Triple(F.getParent()->getTargetTriple());
  return readRegister(B, (TargetTriple.getArch() == Triple::x86_64) ? "rsp" : "sp");
}

static Value *writeRegister(IRBuilder<> &IRB, StringRef Name, Value* val) {
  Module *M = IRB.GetInsertBlock()->getParent()->getParent();
  LLVMContext *C = &(M->getContext());
  Type * Int64Ty = IRB.getInt64Ty();
  auto *WriteRegister = Intrinsic::getDeclaration(M, Intrinsic::write_register, Int64Ty);
  MDNode *MD = MDNode::get(*C, {MDString::get(*C, Name)});
  Value *Args[] = {MetadataAsValue::get(*C, MD), val};
  return IRB.CreateCall(WriteRegister, Args);
}

static Value* setSP(IRBuilder<> &B, Function& F, Value* val) {
  auto TargetTriple = Triple(F.getParent()->getTargetTriple());
  return writeRegister(B, (TargetTriple.getArch() == Triple::x86_64) ? "rsp" : "sp", val);
}


namespace {

  /// \Get global variable
  /// Return the globalVariable datastructure
  /// First argument : Global variable's name
  /// Second argument: Type of Global variable
  /// Third argument : Module
  /// Fourth argument: If it is a local thread variable or not
  GlobalVariable* GetGlobalVariable(const char* GlobalName, Type* GlobalType, Module& M, bool localThread=false){
    GlobalVariable* globalVar = M.getNamedGlobal(GlobalName);
    if(globalVar){
      // If already exists, return it
      return globalVar;
    }
    // If it doesn't exists, construct it now
    globalVar = dyn_cast<GlobalVariable>(M.getOrInsertGlobal(GlobalName, GlobalType));
    globalVar->setLinkage(GlobalValue::ExternalLinkage);
    if(localThread)
      globalVar->setThreadLocal(true);
    return globalVar;
  }

  /// \brief Helper to find a function with the given name, creating it if it
  /// doesn't already exist. If the function needed to be created then return
  /// false, signifying that the caller needs to add the function body.
  bool GetOrCreateFunction(const char *FnName, Module& M,
                           FunctionType*& FTy, Function *&Fn,
                           Function::LinkageTypes Linkage =
                           Function::InternalLinkage,
                           bool DoesNotThrow = true) {
    LLVMContext &Ctx = M.getContext();

    Fn = M.getFunction(FnName);
    if (Fn) {
      return true;
    }
    // Otherwise we have to create it
    Fn = Function::Create(FTy, Linkage, FnName, &M);
    // Set nounwind if it does not throw.
    if (DoesNotThrow)
      Fn->setDoesNotThrow();
    return false;
  }

  FunctionCallee Get__unwindrts_get_nworkers(Module& M) {
    LLVMContext &C = M.getContext();
    AttributeList AL;
    AL = AL.addFnAttribute(C, Attribute::ReadNone);
    AL = AL.addFnAttribute(C, Attribute::NoUnwind);
    FunctionType *FTy = FunctionType::get(Type::getInt32Ty(C), {}, false);
    return M.getOrInsertFunction("__cilkrts_get_nworkers", FTy, AL);
  }


  /// \Create the function that hashes a string
  /// Based on the following computation (from GNU library)
  /// uint32_t hashGnu(const uint8_t* name) {
  ///    uint32_t h = 5381;
  ///    for (; *name; name++) {
  ///      h = (h << 5) + h + *name;
  ///    }
  ///    return h;
  /// }
  /// Returns the function body
  /// First argument : Module
  Function* Get__unwindrts_unwind_gnuhash(Module& M) {
    Function* Fn = nullptr;
    LLVMContext& C = M.getContext();
    FunctionType* unwind_gnuhash_ty = FunctionType::get(Type::getInt32Ty(C), {PointerType::getInt8PtrTy(C)}, false);
    if (GetOrCreateFunction("unwind_gnuhash_llvm", M, unwind_gnuhash_ty, Fn))
      return Fn;

    const DataLayout &DL = M.getDataLayout();

    BasicBlock* entry = BasicBlock::Create(C, "entry", Fn);
    BasicBlock* forbodypreheader = BasicBlock::Create(C, "for.body.preheader", Fn);
    BasicBlock* forbody = BasicBlock::Create(C, "for.body", Fn);
    BasicBlock* forend = BasicBlock::Create(C, "for.end", Fn);
    /*
      define i32 @hashGnu(i8* nocapture readonly %name) local_unnamed_addr #0
      entry:
      %0 = load i8, i8* %name, align 1, !tbaa !2
      %tobool6 = icmp eq i8 %0, 0
      br i1 %tobool6, label %for.end, label %for.body.preheader
    */

    Function::arg_iterator argsIt = Fn->arg_begin();
    Value* args = &*argsIt;

    IRBuilder<> B(entry);
    Value* nameLoad = B.CreateAlignedLoad(Type::getInt8Ty(C), args, Align(1), "nameLoad");
    Value* tobool6 = B.CreateICmpEQ(nameLoad, B.getInt8(0), "tobool6");
    B.CreateCondBr(tobool6, forend, forbodypreheader);

    /*
      for.body.preheader:                               ; preds = %entry
      br label %for.body

      for.body:                                         ; preds = %for.body.preheader, %for.body
      %1 = phi i8 [ %2, %for.body ], [ %0, %for.body.preheader ]
      %h.08 = phi i32 [ %add1, %for.body ], [ 5381, %for.body.preheader ]
      %name.addr.07 = phi i8* [ %incdec.ptr, %for.body ], [ %name, %for.body.preheader ]
      %add = mul i32 %h.08, 33
      %conv = zext i8 %1 to i32
      %add1 = add i32 %add, %conv
      %incdec.ptr = getelementptr inbounds i8, i8* %name.addr.07, i64 1
      %2 = load i8, i8* %incdec.ptr, align 1, !tbaa !2
      %tobool = icmp eq i8 %2, 0
      br i1 %tobool, label %for.end, label %for.body
    */

    B.SetInsertPoint(forbodypreheader);
    B.CreateBr(forbody);
    B.SetInsertPoint(forbody);

    auto charptrphi = B.CreatePHI(IntegerType::getInt8Ty(C), 2, "charptr");
    charptrphi->addIncoming(nameLoad, forbodypreheader);
    auto hashValphi = B.CreatePHI(IntegerType::getInt32Ty(C), 2, "hashVal");
    hashValphi->addIncoming(B.getInt32(5381), forbodypreheader);
    auto namePhi = B.CreatePHI(IntegerType::getInt8Ty(C)->getPointerTo(), 2, "namePhi");
    namePhi->addIncoming(args, forbodypreheader);

    auto add = B.CreateMul(hashValphi, B.getInt32(33), "add");
    auto conv = B.CreateZExt(charptrphi, IntegerType::getInt32Ty(C), "conv");
    auto add1 = B.CreateAdd(add, conv, "add1");
    auto incdecptr = B.CreateConstGEP1_32(IntegerType::getInt8Ty(C), namePhi, 1, "incdecptr");
    auto incdecptrLoad = B.CreateAlignedLoad(IntegerType::getInt8Ty(C), incdecptr, Align(1), "incdecptrLoad");

    charptrphi->addIncoming(incdecptrLoad, forbody);
    hashValphi->addIncoming(add1, forbody);
    namePhi->addIncoming(incdecptr, forbody);

    auto tobool = B.CreateICmpEQ(incdecptrLoad, B.getInt8(0), "tobool");
    B.CreateCondBr(tobool, forend, forbody);

    /*
      for.end:                                          ; preds = %for.body, %entry
      %h.0.lcssa = phi i32 [ 5381, %entry ], [ %add1, %for.body ]
      ret i32 %h.0.lcssa
    */

    B.SetInsertPoint(forend);
    auto finalHashVal = B.CreatePHI(IntegerType::getInt32Ty(C), 2, "finalHashVal");
    finalHashVal->addIncoming(B.getInt32(5381), entry);
    finalHashVal->addIncoming(add1, forbody);
    B.CreateRet(finalHashVal);
    Fn->addFnAttr(Attribute::NoUnwindPath);
    return Fn;
  }


  /// \Create the function that locate the parent's backtrack routine based on the return address of the child
  /// Based on the following computation
  ///
  ///   uint32_t hva = (uint32_t) (hashGnui((const uint32_t) ((uint64_t)ra) ) % nbucket);
  ///   uint32_t query = bucket[hva];
  ///   while((ra !=  ratable[query]) && (query != 0)) {
  ///	  query = chain[query];
  ///   }
  ///   uint32_t uwpath = unwindtable[query];
  ///
  /// Returns the function body
  /// First argument : Module
  Function* Get__unwindrts_unwind_queryunwindaddress(Module& M) {
    LLVMContext& C = M.getContext();
    Function* Fn = nullptr;
    FunctionType* unwind_queryunwindaddress_ty = FunctionType::get(Type::getInt32Ty(C), {Type::getInt64Ty(C)}, false);
    if (GetOrCreateFunction("unwind_queryunwindaddress_llvm", M, unwind_queryunwindaddress_ty, Fn))
      return Fn;

    const DataLayout &DL = M.getDataLayout();

    BasicBlock* entry = BasicBlock::Create(C, "entry", Fn);
    BasicBlock* whilebodypreheader = BasicBlock::Create(C, "while.body.preheader", Fn);
    BasicBlock* whilebody = BasicBlock::Create(C, "while.body", Fn);
    BasicBlock* whileendloopexit = BasicBlock::Create(C, "while.end.loopexit", Fn);
    BasicBlock* whileend = BasicBlock::Create(C, "while.end", Fn);

    Type *Int32Ty    = Type::getInt32Ty(C);
    Type *Int32PtrTy = Type::getInt32PtrTy(C);

    // Global variable
    GlobalVariable* pbucket = GetGlobalVariable("bucket", Int32PtrTy, M, true);
    GlobalVariable* pnbucket = GetGlobalVariable("nbucket", Int32Ty, M, true);
    GlobalVariable* pratable = GetGlobalVariable("ratable", Int32PtrTy, M, true);
    GlobalVariable* pchain = GetGlobalVariable("chain", Int32PtrTy, M, true);
    GlobalVariable* punwindtable = GetGlobalVariable("unwindtable", Int32PtrTy, M, true);

    // First argument
    Function::arg_iterator argsIt = Fn->arg_begin();
    Value* args = &*argsIt;

    // Builder
    IRBuilder<> B(entry);

    auto bucket = B.CreateLoad(Int32PtrTy, pbucket);
    auto chain = B.CreateLoad(Int32PtrTy, pchain);
    auto ratable = B.CreateLoad(Int32PtrTy, pratable);
    auto unwindtable = B.CreateLoad(Int32PtrTy, punwindtable);
    auto nbucket = B.CreateLoad(Int32Ty, pnbucket);

    /*
      entry:
      %0 = inttoptr i64 %ra to i8*
      %call = tail call i32 @hashGnu(i8* %0)
      %1 = load i32, i32* @nbucket, align 4, !tbaa !5
      %rem = urem i32 %call, %1
      %idxprom = zext i32 %rem to i64
      %arrayidx = getelementptr inbounds [10 x i32], [10 x i32]* @bucket, i64 0, i64 %idxprom
      %query.016 = load i32, i32* %arrayidx, align 4, !tbaa !5
      %conv = trunc i64 %ra to i32
      %idxprom117 = zext i32 %query.016 to i64
      %arrayidx218 = getelementptr inbounds [10 x i32], [10 x i32]* @ratable, i64 0, i64 %idxprom117
      %2 = load i32, i32* %arrayidx218, align 4, !tbaa !5
      %cmp19 = icmp ne i32 %2, %conv
      %cmp420 = icmp ne i32 %query.016, 0
      %3 = and i1 %cmp420, %cmp19
      br i1 %3, label %while.body.preheader, label %while.end
    */

    auto loadRAi8 = B.CreateCast(Instruction::IntToPtr, args,
                                 IntegerType::getInt8Ty(C)->getPointerTo(), "returnaddrptr");

#if 0
    FunctionCallee gnuhash = UNWINDRTS_FUNC(unwind_gnuhash, M);
    CallInst* hashVal = B.CreateCall(gnuhash, {loadRAi8}, "hashVal");
#else
    auto args32 = B.CreateTrunc(args, IntegerType::getInt32Ty(C));
    FunctionCallee hashGnui = Get_hashGnui(M);
    CallInst* hashVal = B.CreateCall(hashGnui, {args32});
#endif

    auto rem = B.CreateURem(hashVal, nbucket, "rem");
    auto idxprom = B.CreateZExt(rem, IntegerType::getInt64Ty(C), "idxprom");

    auto arrayidx = B.CreateInBoundsGEP(Type::getInt32Ty(C), bucket, idxprom, "arrayidx");
    auto query016 = B.CreateAlignedLoad(Type::getInt32Ty(C), arrayidx, Align(4), "query.016");
    auto conv = B.CreateTrunc(args,  IntegerType::getInt32Ty(C), "conv");
    auto idxprom117 = B.CreateZExt(query016, IntegerType::getInt64Ty(C), "idxprom117");
    auto arrayidx218 = B.CreateInBoundsGEP(Type::getInt32Ty(C), ratable, idxprom117, "arrayidx218");
    auto arrayidx218Load = B.CreateAlignedLoad(Type::getInt32Ty(C), arrayidx218, Align(4), "arrayidx218Load");
    auto cmp19 = B.CreateICmpNE(arrayidx218Load, conv, "cmp19");
    auto cmp420 = B.CreateICmpNE(query016, B.getInt32(0), "cmp420");
    auto andCmp = B.CreateAnd(cmp19, cmp420, "andCmp");
    B.CreateCondBr(andCmp, whilebodypreheader, whileend);

    /*
      while.body.preheader:                             ; preds = %entry
      br label %while.body

      while.body:                                       ; preds = %while.body.preheader, %while.body
      %idxprom121 = phi i64 [ %idxprom1, %while.body ], [ %idxprom117, %while.body.preheader ]
      %arrayidx7 = getelementptr inbounds [10 x i32], [10 x i32]* @chain, i64 0, i64 %idxprom121
      %query.0 = load i32, i32* %arrayidx7, align 4, !tbaa !5
      %idxprom1 = zext i32 %query.0 to i64
      %arrayidx2 = getelementptr inbounds [10 x i32], [10 x i32]* @ratable, i64 0, i64 %idxprom1
      %3 = load i32, i32* %arrayidx2, align 4, !tbaa !5
      %cmp = icmp ne i32 %3, %conv
      %cmp4 = icmp ne i32 %query.0, 0
      %4 = and i1 %cmp4, %cmp
      br i1 %4, label %while.body, label %while.end.loopexit
    */

    B.SetInsertPoint(whilebodypreheader);
    B.CreateBr(whilebody);

    B.SetInsertPoint(whilebody);
    auto idxprom121 = B.CreatePHI(IntegerType::getInt64Ty(C), 2, "idxprom121");
    idxprom121->addIncoming(idxprom117, whilebodypreheader);
    auto arrayidx7 = B.CreateInBoundsGEP(Type::getInt32Ty(C), chain, idxprom121, "arrayidx7");
    auto query0 = B.CreateAlignedLoad(Type::getInt32Ty(C), arrayidx7, Align(4), "query.0");
    auto idxprom1 = B.CreateZExt(query0, IntegerType::getInt64Ty(C), "idxprom1");
    auto arrayidx2 = B.CreateInBoundsGEP(Type::getInt32Ty(C), ratable, idxprom1, "arrayidx2");
    auto arrayidx2load = B.CreateAlignedLoad(Type::getInt32Ty(C), arrayidx2, Align(4), "arrayidx2Load");
    auto cmp = B.CreateICmpNE(arrayidx2load, conv, "cmp");
    auto cmp4 = B.CreateICmpNE(query0, B.getInt32(0), "cmp4");
    auto andCmp2 = B.CreateAnd(cmp4, cmp, "andCmp2");
    B.CreateCondBr(andCmp2, whilebody, whileendloopexit);

    idxprom121->addIncoming(idxprom1, whilebody);

    /*
      while.end.loopexit:                               ; preds = %while.body
      %idxprom1.le = zext i32 %query.0 to i64
      br label %while.end

      while.end:                                        ; preds = %while.end.loopexit, %entry
      %idxprom1.lcssa = phi i64 [ %idxprom117, %entry ], [ %idxprom1.le, %while.end.loopexit ]
      %5 = load i32*, i32** @unwindtable, align 8, !tbaa !7
      %arrayidx9 = getelementptr inbounds i32, i32* %5, i64 %idxprom1.lcssa
      %6 = load i32, i32* %arrayidx9, align 4, !tbaa !5
      ret i32 %6
    */

    B.SetInsertPoint(whileendloopexit);
    auto idxprom1le = B.CreateZExt(query0, IntegerType::getInt64Ty(C), "idxprom1.le");
    B.CreateBr(whileend);

    B.SetInsertPoint(whileend);
    auto idxprom1lcssa = B.CreatePHI(IntegerType::getInt64Ty(C), 2, "idxprom1.lcssa");
    idxprom1lcssa->addIncoming(idxprom117, entry);
    idxprom1lcssa->addIncoming(idxprom1le, whileendloopexit);
    auto arrayidx9 = B.CreateInBoundsGEP(Type::getInt32Ty(C), unwindtable, idxprom1lcssa, "arrayidx9");
    B.CreateRet(B.CreateAlignedLoad(Type::getInt32Ty(C), arrayidx9, Align(4)));

    llvm::InlineFunctionInfo ifi;
    llvm::InlineFunction(*(hashVal), ifi, nullptr, true);
    Fn->addFnAttr(Attribute::NoUnwindPath);
    return Fn;
  }

  // Return the early set of Value* that is used by Dst and that dominates the Dst
  // First argument: Dst variable
  // Second argument: DT dominator tree
  // Third argument: insertPt
  // Fourt argument : Srcs, used to store the output
  void findRootArgument(Value* Dst, DominatorTree& DT, Instruction* InsertPt, SmallSet<Value*, 4>& Srcs) {
    if(isa<Argument>(Dst)) {
      Srcs.insert(Dst);
      return;
    }

    if(isa<GlobalVariable>(Dst)) {
      Srcs.insert(Dst);
      return;
    }

    if(!isa<Instruction>(Dst))
      return;

    if(DT.dominates(Dst, InsertPt)) {
      Srcs.insert(Dst);
      return;
    }

    Instruction* SInst = dyn_cast<Instruction>(Dst);
    unsigned nOp = SInst->getNumOperands();
    for (unsigned i = 0; i<nOp; i++) {
      auto opVal = SInst->getOperand(i);
      findRootArgument(opVal, DT, InsertPt, Srcs);
    }
    return;
  }

  // Store the Instruction that allows the construction of Dst using Src
  // First argument : Destination
  // Second argument : Source
  // Third argument : Insts2Clone (output), store the instruction that lead to Dst from Src
  // Fourth argument : InstsSet (output). Similar to third argument, but store it in a set.
  void findPathToDst(Value *Dst, Value *Src, SmallVector<Instruction*, 8>& Insts2Clone, SmallSet<Instruction*, 8>& InstsSet) {
    if(!isa<Instruction>(Dst))
      return;

    Instruction* DInst = dyn_cast<Instruction>(Dst);
    if(InstsSet.count(DInst) > 0)
      return;

    InstsSet.insert(DInst);

    if(!isa<PHINode>(DInst))
      Insts2Clone.push_back(dyn_cast<Instruction>(DInst));
    if (Dst == Src)
      return;

    unsigned nOp = DInst->getNumOperands();
    for (unsigned i = 0; i<nOp; i++) {
      auto opVal = DInst->getOperand(i);
      // Push copied instruction into set
      findPathToDst(opVal, Src, Insts2Clone, InstsSet);
    }
  }

  // Return a function wrapper for the parallel task inside a det.achd block in the slowpath.
  // The wrapper is used in the slow path and contains the routine to push and pop parallel tasks.
  // A wrapper is needed to prevent race condition on a s shared variables being used by parallel tasks.
  // For example, is induction variable in DAC-TRE.
  // First argument (In) : Represent the call instruction that needs a wrapper
  // Second argument (In) : Represent instruction used in wrapper but defined outside det.achd
  // Third argument (In) : Additional instruction that should be inside the wrapper (e.g., storing the result of the function to memory)
  // Fourth argument (In) : Represent the type of the workctx (workctx is an argument used by the function wrapper)
  /*
    Example:
    define internal fastcc void @"\90\F2]\01Wrapper"(i32 %0, %struct.InternalNode* %1, %struct.InternalNode* %2, %struct.InternalNode* %3, i8** %4, i8* %5, %struct.InternalNode** %6) unnamed_addr #29 {
    entry:
      call void @push_workctx(i8** %4, i8* %5)
      %7 = call %struct.InternalNode* @mul_and_subT(i32 %0, i32 0, %struct.InternalNode* %1, %struct.InternalNode* %2, %struct.InternalNode* %3)
      store volatile %struct.InternalNode* %7, %struct.InternalNode** %6, align 8, !tbaa !11
      call void @pop_workctx(i8** %4, i8* %5)
      ret void
    }
   */
  Function* generateWrapperFuncForSlowPath(CallInst* CI, SmallPtrSet<Value*, 8> OutsideVars, SmallVector<Instruction *, 4>& insts2clone, Type* workCtxType){
    // Get the function that needs a wrapper
    Function& F = *CI->getCalledFunction();
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();

    const DataLayout &DL = M->getDataLayout();
    auto InternalLinkage = Function::LinkageTypes::InternalLinkage;

    ValueToValueMapTy VMapGotStolenI;

    // If function have already been constructed, return it immediately
    auto Name = "__prsc_" + F.getName() + "Wrapper";
    auto Fn = M->getFunction(Name.str());
    if (Fn)
      return Fn;

    // Function return is of type void
    Type *VoidTy = Type::getVoidTy(C);
    FunctionType *FTy = F.getFunctionType();
    assert(!FTy->isFunctionVarArg());
    Type *RetType = FTy->getReturnType();

    // Routine to manage the parallel tasks in the slow path deque
    FunctionCallee PUSH_WORKCTX = Get_push_workctx(*M);
    FunctionCallee POP_WORKCTX = Get_pop_workctx(*M);

    // Create the function type
    SmallVector<Type *, 8> WrapperParamTys(FTy->param_begin(), FTy->param_end());
    WrapperParamTys.push_back(workCtxType);
    WrapperParamTys.push_back(IntegerType::getInt8Ty(C)->getPointerTo());

    if(!RetType->isVoidTy()) {
      for(auto OutsideVar: OutsideVars) {
        WrapperParamTys.push_back(OutsideVar->getType());
      }
    }
    FunctionType *WrapperFTy = FunctionType::get(VoidTy, WrapperParamTys, /*isVarArg=*/false);

    // Create the function
    Function *Wrapper = Function::Create(WrapperFTy, InternalLinkage, Name, M);
    BasicBlock *Entry = BasicBlock::Create(C, "entry", Wrapper);

    unsigned sizeOfOutput = OutsideVars.size();

    unsigned endIdx = 2; // void** ctx, void* rsp
    if(!RetType->isVoidTy())
      endIdx = endIdx + sizeOfOutput; // void** ctx, void* rsp, storage*

    IRBuilder<> B(Entry);

    // Call the original function
    SmallVector<Value*, 8> Args;
    for (auto it = Wrapper->arg_begin(); it < Wrapper->arg_end() - endIdx; ++it) {
      Args.push_back(it);
    }

    auto ctxArg = Wrapper->arg_end() - (endIdx);
    auto rspArg = Wrapper->arg_end() - (endIdx-1);
    auto pointerArg= Wrapper->arg_end() - 1;

    // Push the continuation to the slowpath deque
    auto res0 = B.CreateCall(PUSH_WORKCTX, {ctxArg, rspArg});
    res0->setTailCall(false);

    // Call the original function
    CallInst *Result = B.CreateCall(&F, Args);
    Result->setTailCall(false);

    // Insert instruction that comes after the function call in det.achd
    if (!RetType->isVoidTy()){
     Instruction* insertInst = Result;
      for(auto ii: insts2clone) {
        Instruction * iiClone = ii->clone();
        iiClone->insertAfter(insertInst);
        VMapGotStolenI[ii] = iiClone;
        insertInst = iiClone;
        if(isa<StoreInst>(iiClone)) {
          dyn_cast<StoreInst>(iiClone)->setVolatile(true);
        }
      }

      // Update the uses of instruction of the original call in both wrapper and gotstolen (sync) handler
      for(auto ii: insts2clone) {
	// For those instruction, update their uses with variables inside the wrapper or the wrapper's argumetn
	for (Use &U : ii->operands()) {
          Value *v = U.get();
          if(v == CI) {
	    // Use the result of the function call
            SmallVector< Use*, 4 >  useNeed2Update;
            // Can be converted into a function
	    for (auto &use : v->uses()) {
              auto * user = dyn_cast<Instruction>(use.getUser());
              if(user->getParent() == Entry)
                useNeed2Update.push_back(&use);
            }
            for( auto U : useNeed2Update ){
              U->set(Result);
            }
          } else {
	    // Use defined outside det.achd, need to locate use from argument.
            unsigned argLoc = sizeOfOutput+1;
            for(auto OutsideVar : OutsideVars) {
              argLoc--;
              if(v == OutsideVar) {
                SmallVector< Use*, 4 >  useNeed2Update;
                for (auto &use : v->uses()) {
                  auto * user = dyn_cast<Instruction>(use.getUser());
                  if(user->getParent() == Entry)
                    useNeed2Update.push_back(&use);
                }
                for( auto U : useNeed2Update ){
                  U->set(Wrapper->arg_end() - argLoc);
                }
              }
            }
          }
        }

	// For instruction that is in the gotstolen routine,
	// also update their uses.
        /*
	  gotstolenhandlerEntry210:                         ; preds = %det.achd37
	  %88 = retpad %struct.InternalNode*
	  ....
	  store volatile %struct.InternalNode* %88, %struct.InternalNode** %a01, align 8, !tbaa !11
	  call void @suspend2scheduler(i32 %locVal217, i32 %owner.0.owner.0.owner.0.owner.0.ownerVal218, i32 0) #26
	  unreachable
	 */
	// Should move this routine to a different function?
	SmallVector< Use*, 4 >  useNeed2Update;
        Instruction * gotStolenI = dyn_cast<Instruction>(VMapGotStolenI[ii]);
        for (auto &use : ii->uses()) {
          auto * user = dyn_cast<Instruction>(use.getUser());
          if(user->getParent() == Entry) {
            useNeed2Update.push_back(&use);
          }
        }
        for( auto U : useNeed2Update ){
          U->set(gotStolenI);
        }
      }
    }

    // Pop the continuation
    auto res1 = B.CreateCall(POP_WORKCTX, {ctxArg, rspArg});
    res1->setTailCall(false);

    // Return
    B.CreateRetVoid();
    return Wrapper;
  }

  // Return basic blocks to clone to create wrapper for inlined parallel task.
  // Used to create a function wrapper for forks that have been inlined
  // First argument (I): detach basic block (det.achd)
  // Second argument (O) : Basic block to clones. Used to create a function wrapper for forks that have been inlined.
  // Basic block consists a path from detach to reattach
  void traverseDetach(BasicBlock* detachBB, SmallVector<BasicBlock*, 4>& bb2clones) {
    SmallVector<BasicBlock*, 4> bbList;
    ValueMap<BasicBlock*, bool> haveVisited;
    BasicBlock* bb = nullptr;

    // Root is the detachBB
    bbList.push_back(detachBB);
    while(!bbList.empty()) {
      // Visit basic block
      bb = bbList.back();
      bbList.pop_back();

      // A reattach or multiretcall indicate a transition to the continuation.
      // Stop here
      if( isa<ReattachInst>(bb->getTerminator()) ) {
        bb2clones.push_back(bb);
        continue;
      } else if (isa<MultiRetCallInst>(bb->getTerminator()) ) {
	// If we have converted it into multiretcall
	bb2clones.push_back(bb);
        continue;
      }

      // Basic block already visited, skip
      if(haveVisited.lookup(bb)){
        continue;
      }

      // Mark bb as visited
      haveVisited[bb] = true;
      bb2clones.push_back(bb);

      // Traverse the sucessor of the current basic blcok
      for ( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {
        auto succBB = *SI;
        bbList.push_back(succBB);
      }
    }
    return;
  }

  // Return basic block that contain the reattach instruction.
  // Can be combine with the above function since it is simialr
  // Get the actual detach basic block that contains the call
  BasicBlock* getBBContainReattached(BasicBlock* detachBB) {
    SmallVector<BasicBlock*, 4> bbList;
    ValueMap<BasicBlock*, bool> haveVisited;
    BasicBlock* bb = nullptr;
    BasicBlock* resBB = nullptr;

    bbList.push_back(detachBB);
    while(!bbList.empty()) {
      // Visit basic block
      bb = bbList.back();
      bbList.pop_back();

      // If reattach is found, then the call is located in this basic block?
      // Need to double check?
      if( isa<ReattachInst>(bb->getTerminator()) ) {
        resBB = bb;
        break;
      } else if (isa<MultiRetCallInst>(bb->getTerminator()) ) {
        resBB = bb;
        break;
      }

      // Basic block already visited, skip
      if(haveVisited.lookup(bb)){
        continue;
      }

      // Mark bb as visited
      haveVisited[bb] = true;

      for ( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {
        auto succBB = *SI;
        bbList.push_back(succBB);
      }
    }

    assert(resBB && "no function call contain in detach");
    return resBB;
  }

  // Check if instruction is not a phi instruction, or dbginfo instruction, or lifetime instruction, or sync start instruction
  bool isNonPHIOrDbgOrLifetime(Instruction * I) {
    if (isa<PHINode>(I) || isa<DbgInfoIntrinsic>(I))
      return false;
    if (auto *II = dyn_cast<IntrinsicInst>(I))
      if (II->getIntrinsicID() == Intrinsic::lifetime_start ||
          II->getIntrinsicID() == Intrinsic::lifetime_end ||
          II->getIntrinsicID() == Intrinsic::syncregion_start)
        return false;
    return true;
  }

  // Add potentialJump using multiretcall
  // Instuction* insertPoint: Is the point of insertion
  // SmallVector<BasicBlock*, 4> &indirectBBs : List of indirect basic block where multiretcall can return to
  // Return the default continuation
  BasicBlock* insertPotentialJump(Instruction *insertPoint, SmallVector<BasicBlock*, 4> &indirectBBs){
    BasicBlock* bb = insertPoint->getParent();
    Function* F = bb->getParent();
    Module* M = F->getParent();
    LLVMContext& C = M->getContext();
    IRBuilder<> B(C);

    // Split the basic block, afterBB is the default continuation of multiretcall
    auto afterBB = bb->splitBasicBlock(insertPoint->getNextNode());
    auto terminator = bb->getTerminator();
    auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);

    // Replace the terminator with the MultiRetCall
    B.SetInsertPoint(bb);
    auto res = B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), afterBB, indirectBBs, {});

    // delete the call instruction
    terminator->eraseFromParent();

    // return default continuation
    return afterBB;
  }

  // Replace a fork with MultiRetCall function that has new two indirect bb: slowpathentry and gotstolenhandler
  // CallInst* ci: The fork instruction to convert to multiretcall IR
  // Function& F: The function where ci resides (redundant?)
  // Return the multiretcallinst
  MultiRetCallInst* replaceForkWithMultiRetCall(CallInst *ci, Function& F) {
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();
    IRBuilder<> B(C);

    // Split basic block
    auto bb = ci->getParent();
    auto afterBB = bb->splitBasicBlock(ci->getNextNode());
    auto terminator = bb->getTerminator();

    // Prepare the argument
    SmallVector<Value *, 4> args;
    unsigned nArgs = ci->arg_size ();
    for(unsigned i=0; i<nArgs; i++){
      args.push_back(ci->getArgOperand(i));
    }

    // Prepare the indirect destinations
    SmallVector<BasicBlock *, 4> indirectDests;
    std::vector<string> nameBB = {"slowPathEntry", "gotstolenhandlerEntry"};
    for(int i=0; i<nameBB.size(); i++){
      BasicBlock * bb = BasicBlock::Create(C, nameBB.at(i), &F);
      indirectDests.push_back(bb);
    }

    // Create MultiRetCall
    MultiRetCallInst* mrc = MultiRetCallInst::Create(ci->getCalledFunction(), afterBB, indirectDests, args);
    mrc->setCallingConv(ci->getCallingConv());

    // Replace the fork with multiretcall
    ReplaceInstWithInst(ci, mrc);

    // Add retpad to the default continuation
    B.SetInsertPoint(afterBB->getFirstNonPHIOrDbgOrLifetime());
    auto newCall = B.CreateRetPad(mrc);

    // delete the call instruction
    terminator->eraseFromParent();

    return mrc;
  }

  // Convert a basic block into a function
  // Function& F : Function of the bb2clones
  // BasicBlock* mainBB : Use as the name of the Fcn
  // bb2clones: Basic blocks that is used to construct the wrapper function
  // fcnArgs: Arguments for the new wrapper function
  // Return the wrapper function.
  Function* convertBBtoFcn (Function& F, BasicBlock* mainBB, SmallVector<BasicBlock*, 4>& bb2clones, SmallPtrSet<Value*, 4>& fcnArgs) {
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();

    const DataLayout &DL = M->getDataLayout();
    auto InternalLinkage = Function::LinkageTypes::InternalLinkage;

    // Check if function is already created
    auto Name = mainBB->getName() + F.getName()  + "_W";
    auto NameStr = Name.str().substr(0,255);
    auto Fn = M->getFunction(NameStr);
    if (Fn)
      return Fn;

    // Function return void and usses fcnArgs as the argument type
    Type *VoidTy = Type::getVoidTy(C);
    SmallVector<Type *, 8> WrapperParamTys;
    for(auto fcnArg: fcnArgs) {
      WrapperParamTys.push_back(dyn_cast<Value>(fcnArg)->getType());
    }

    FunctionType *WrapperFTy = FunctionType::get(VoidTy, WrapperParamTys, /*isVarArg=*/false);
    Function *Wrapper = Function::Create(WrapperFTy, InternalLinkage, NameStr, M);

    ValueToValueMapTy VMapSlowPath;
    ValueToValueMapTy VMapSlowPathReverse;

    // Used for debugging, still not exactly sure how it works
    DebugInfoFinder DIFinder;
    DISubprogram *SP = F.getSubprogram();
#if 1
    if (SP) {
      // Add mappings for some DebugInfo nodes that we don't want duplicated
      // even if they're distinct.
      auto &MD = VMapSlowPath.MD();
      MD[SP->getUnit()].reset(SP->getUnit());
      MD[SP->getType()].reset(SP->getType());
      MD[SP->getFile()].reset(SP->getFile());
      MD[SP].reset(SP);
    }
#else
    for (DISubprogram *ISP : DIFinder.subprograms())
      if (ISP != SP)
        VMapSlowPath.MD()[ISP].reset(ISP);

    for (DICompileUnit *CU : DIFinder.compile_units())
      VMapSlowPath.MD()[CU].reset(CU);

    for (DIType *Type : DIFinder.types())
      VMapSlowPath.MD()[Type].reset(Type);

    // Duplicate the metadata that is attached to the cloned function.
    // Subprograms/CUs/types that were already mapped to themselves won't be
    // duplicated.
    SmallVector<std::pair<unsigned, MDNode *>, 1> MDs;
    F.getAllMetadata(MDs);
    for (auto MD : MDs) {
      auto remapFlag = RF_IgnoreMissingLocals | RF_ReuseAndMutateDistinctMDs;//RF_NullMapMissingGlobalValues| RF_ReuseAndMutateDistinctMDs;
      Wrapper->addMetadata(
                           MD.first,
                           *MapMetadata(MD.second, VMapSlowPath,
                                        F.getSubprogram() != nullptr ? RF_None | remapFlag : RF_NoModuleLevelChanges | remapFlag,
                                        nullptr, nullptr));
    }
#endif

    // Clone bb2clones to create function body
    for (auto pBB : bb2clones){
      VMapSlowPath[pBB] = CloneBasicBlock(pBB, VMapSlowPath, ".wrapper", Wrapper, nullptr, &DIFinder);
      VMapSlowPathReverse[VMapSlowPath[pBB]] = pBB;
    }

    int argCnt = 0;

    // Iterate through the fcnargs
    for(auto fcnArg: fcnArgs) {
      // Get the wrapper's argument
      Function::arg_iterator args = Wrapper->arg_begin()+argCnt;
      Argument* fcnArgIWrapper =  &*args;
      auto fcnArgI = dyn_cast<Value>(fcnArg);

      // Replace variables define outside bb2clones with argument
      fcnArgI->replaceUsesWithIf(fcnArgIWrapper, [&](Use &U) {
          auto *I = dyn_cast<Instruction>(U.getUser());
          // Replace if it's an instruction inside the wrapper.
          return !I || I->getParent()->getParent() == Wrapper;
        });

      // Replace / udpate the Debug instruction inside the wrapper
      SmallVector<DbgVariableIntrinsic *> DbgUsers;
      findDbgUsers(DbgUsers, fcnArgI);
      for (auto *DVI : DbgUsers) {
        if (DVI->getParent()->getParent() == Wrapper)
          DVI->replaceVariableLocationOp(fcnArgI, fcnArgIWrapper);
      }
      argCnt++;
    }

    // --------------------------------------------------------------
    // Update instruction inside the wrapper
    for(auto pBB : bb2clones) {
      BasicBlock * ClonedBB = dyn_cast<BasicBlock>(VMapSlowPath[pBB]);

      // Replace the reattach with a return instruction
      Instruction * termInst = ClonedBB->getTerminator();
      if(isa<ReattachInst>(termInst) ){
        Instruction* returnInst = ReturnInst::Create(C);
        ReplaceInstWithInst(termInst, returnInst);
      }

      // Remap the cloned instruction
      for (Instruction &II : *ClonedBB) {
        //auto remapFlag = RF_NullMapMissingGlobalValues| RF_ReuseAndMutateDistinctMDs;
        auto remapFlag = RF_IgnoreMissingLocals | RF_ReuseAndMutateDistinctMDs;
        RemapInstruction(&II, VMapSlowPath, F.getSubprogram() != nullptr? RF_None | remapFlag  : RF_NoModuleLevelChanges | remapFlag, nullptr, nullptr);
      }
    }

    // Not excalty sure how this works
    // Register all DICompileUnits of the old parent module in the new parent
    // module
    auto *OldModule = F.getParent();
    auto *NewModule = Wrapper->getParent();
    if (OldModule && NewModule && OldModule != NewModule &&
        DIFinder.compile_unit_count()) {
      auto *NMD = NewModule->getOrInsertNamedMetadata("llvm.dbg.cu");
      // Avoid multiple insertions of the same DICompileUnit to NMD.
      SmallPtrSet<const void *, 8> Visited;
      for (auto *Operand : NMD->operands())
        Visited.insert(Operand);
      for (auto *Unit : DIFinder.compile_units())
        // VMap.MD()[Unit] == Unit
        if (Visited.insert(Unit).second)
          NMD->addOperand(Unit);
    }

    // Return wrapper
    return Wrapper;
  }


  // Generate wrapper function for a inlined fork inside a det.achd block
  // Function &F : Function where the detach resides
  // SmallVector<DetachInst*, 4>& seqOrder: How to iterate detach inst without loop
  // SmallVector<DetachInst*, 4>& loopOrder: How to iterate detach inst for loop
  // DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin: Live in variable for det.achd. Stores variabble only used inside the inlined tasks
  void generateWrapperFuncForDetached (Function &F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,
                                       DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin) {
    // Locate the detach instruct
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();
    IRBuilder<> B(C);

    SmallVector<DetachInst*, 4> bbOrder;
    bbOrder.append(seqOrder.begin(), seqOrder.end());
    bbOrder.append(loopOrder.begin(), loopOrder.end());

    // Process the detachInst in certain order
    for (auto detachInst: bbOrder) {
      BasicBlock* pBB = detachInst->getParent();
      assert(pBB);
      BasicBlock* detachBBOri = detachInst->getDetached();
      auto detachBB = getBBContainReattached(detachBBOri);
      BasicBlock* continueBB  = detachInst->getContinue();

      // Store the instruction inside detachBB in a vector
      SmallVector<Instruction *, 4> instsVec;
      for ( auto &II : *detachBB ) {
        instsVec.push_back(&II);
      }

      // Look for the spawn function
      bool bFailToLocateSpawnFunction = true;
      for (auto ii : instsVec) {
        LLVM_DEBUG(dbgs() << "II: " << *ii << "\n");
        if ((isa<CallInst>(ii) || isa<InvokeInst>(ii)) && isNonPHIOrDbgOrLifetime(ii) ) {
          // If we found multiple call inst, need to create wrapper
          if(!bFailToLocateSpawnFunction || isa<IntrinsicInst>(ii)) {
            bFailToLocateSpawnFunction = true;
            break;
          }

	  // If we found only one call inst
          bFailToLocateSpawnFunction = false;
        }
      }

      // If we are able to locate a spawn instruction, process the next detach instruction.
      if(!bFailToLocateSpawnFunction) continue;

      // If we are unable to locate a spawn instruction, create a wrapper
      LLVM_DEBUG(dbgs() << "Need to generate function for inst: " << *detachInst << "\n");

      // Find the basicBlock needed to clone
      SmallVector<BasicBlock*, 4> bb2clones;
      SmallPtrSet<Value*, 4> setBb2clones;
      SmallPtrSet<Value*, 4> fcnArgs;

      // Clone the basic block from detach until reach reattach
      traverseDetach(detachBBOri, bb2clones);
      for(auto bb2clone: bb2clones) {
	setBb2clones.insert(bb2clone);
      }

      // LiveInVar determines the function argument
      // Find live instruction into (LIVE-IN) the basic block of the first detach function, create arguments for this live variable
      auto liveInVars = LVin[detachBBOri][detachBBOri->getUniquePredecessor()];

      LLVM_DEBUG(dbgs() << "For basic block " << detachBBOri->getName() << " live variables in: \n");

      // Since in cilk, the return variable is immediately stored in memory, there should be no live variables
      // Look for live variables inside
      for (auto liveInVar : liveInVars) {
	if(liveInVar->getType()->isTokenTy()) {
	  LLVM_DEBUG(dbgs() << "Ignore token:" << *liveInVar << "\n");
	  continue;
	}

	// Insert live variables where the uses is inside the clone basic block
	for (auto &use : liveInVar->uses()) {
	  auto * user = dyn_cast<Instruction>(use.getUser());
	  if(setBb2clones.find(user->getParent()) != setBb2clones.end()) {
	    LLVM_DEBUG(dbgs() << *liveInVar << "\n");
	    fcnArgs.insert(liveInVar);
	  }
	}
      }

      // Also take into account function arguments
      for(auto it = F.arg_begin(); it != F.arg_end(); it++) {
	for (auto &use : it->uses()) {
	  auto * user = dyn_cast<Instruction>(use.getUser());
	  if(setBb2clones.find(user->getParent()) != setBb2clones.end()) {
	    LLVM_DEBUG(dbgs() << *it << "\n");
	    fcnArgs.insert(it);
	  }
	}

	// Update debug instruction
	SmallVector<DbgVariableIntrinsic *> DbgUsers;
	findDbgUsers(DbgUsers, it);
	for (auto *DVI : DbgUsers) {
	  if ( setBb2clones.find(DVI->getParent()) != setBb2clones.end() ) {
	    fcnArgs.insert(it);
	  }
	}
      }

      LLVM_DEBUG(dbgs() << "Basicblock to clone: " << "\n");
      for(auto bb2clone: bb2clones) {
	LLVM_DEBUG(dbgs() << "BB : " << bb2clone->getName() << "\n");

	// Find debug variable that uses variable that do not belong to live variable or inside wrapper
	for(auto &ii: *bb2clone) {
	  if(isa<DbgInfoIntrinsic>(&ii)) {
	    auto dbgInst = dyn_cast<DbgVariableIntrinsic>(&ii);
	    auto dbgArg = dbgInst->getVariableLocationOp(0);
	    bool shouldInsertVal = isa<Argument>(dbgArg) && fcnArgs.find(dbgArg) == fcnArgs.end();
	    shouldInsertVal = shouldInsertVal || (isa<Instruction>(dbgArg) &&
						  fcnArgs.find(dbgArg) == fcnArgs.end() &&
						  setBb2clones.find(dyn_cast<Instruction>(dbgArg)->getParent()) ==  setBb2clones.end());

	    if(shouldInsertVal) {
	      fcnArgs.insert(dbgArg);
	    }
	  }
	}
      }

      // Create the function
      Function* wrapper = convertBBtoFcn(F, detachBBOri , bb2clones, fcnArgs);
      wrapper->addFnAttr(Attribute::NoInline);
      wrapper->addFnAttr("no-frame-pointer-elim");
      auto bbContainReattach = getBBContainReattached(detachBBOri);

      // Erase all instruction except reattach
      SmallVector<Instruction *, 4> inst2delete;
      for(auto &ii : *bbContainReattach) {
	if(isa<ReattachInst>(&ii))
	  break;

	inst2delete.push_back(&ii);
      }
      for(auto it = inst2delete.rbegin(); it != inst2delete.rend(); it++){
	(*it)->eraseFromParent();
      }


      // Replace the reattach with a call to the wrapper
      B.SetInsertPoint(bbContainReattach->getTerminator());
      SmallVector<Value*, 4> fcnArgVectors(fcnArgs.begin(), fcnArgs.end());
      B.CreateCall(wrapper, fcnArgVectors);

      // Update detach instruction
      detachInst->setSuccessor(0, bbContainReattach);

    }
    return ;
  }


  // Insert poll and exit condition if parallelism has been realized in par-for-seq
  /*
    define private fastcc void @_Z3fooi.outline_pfor.cond.ls1.1par-for-seq(i32 %__begin.0.start.ls1, i32 %end.ls1, i32 %grainsize.ls1, i32* align 8 %ivStorage.ls1) unnamed_addr #3 {
    pfor.cond.preheader.ls1:
      // Initialize the parallelism status to false
      %bHaveUnwind = alloca i1, align 1
      store i1 false, i1* %bHaveUnwind, align 1

      br label %pfor.inc.ls1

    pfor.inc.ls1:                                   ; preds = %8, %pfor.cond.preheader.ls1
      %__begin.0.ls1 = phi i32 [ %9, %8 ], [ %__begin.0.start.ls1, %pfor.cond.preheader.ls1 ]
      // Insert poll
      __builtin_poll();

      // Check if parallelism has been realized, if so return
      %bHaveUnwind.0.bHaveUnwind.0.bHaveUnwind.0.bHaveUnwind.0.1 = load volatile i1, i1* %bHaveUnwind, align 1
      br i1 %bHaveUnwind.0.bHaveUnwind.0.bHaveUnwind.0.bHaveUnwind.0.1, label %common.ret, label %8

    8:                                                ; preds = %unwind_ulifsim2_llvm.exit
      store i8 1, i8* getelementptr inbounds (%struct._request_channel, %struct._request_channel* @req_local, i64 0, i32 2), align 2
      %9 = add i32 %__begin.0.ls1, 1

      // body of function

      %exitcond.not.ls1 = icmp eq i32 %9, %end.ls1
      br i1 %exitcond.not.ls1, label %pfor.cond.cleanup.ls1, label %pfor.inc.ls1, !llvm.loop !11

    pfor.cond.cleanup.ls1:                            ; preds = %8
    ....

    }
  */
  void instrumentLoop (Function *F, Loop* CurrentLoop, Value* bHaveUnwindAlloc) {
    Module *M = F->getParent();
    LLVMContext& C = M->getContext();
#ifdef PRL_LATER
    IRBuilder<> B(F->getEntryBlock().getFirstNonPHIOrDbgOrLifetime());
    const DataLayout &DL = M->getDataLayout();
    Type *VoidPtrTy  = PointerType::getInt8PtrTy(C);

    // TODO: CNP At the start of the function record the return address
    auto addrOfRA = Intrinsic::getDeclaration(M, Intrinsic::addressofreturnaddress, {VoidPtrTy});
    Value* myRA = B.CreateCall(addrOfRA);
    myRA = B.CreateBitCast(myRA, IntegerType::getInt64Ty(C)->getPointerTo());
    Value* myRAStorage = B.CreateAlloca(IntegerType::getInt64Ty(C), DL.getAllocaAddrSpace(), nullptr, "myra");
    B.CreateStore(B.CreateLoad(IntegerType::getInt64Ty(C), myRA, 1), myRAStorage, true);
#else
    IRBuilder<> B(M->getContext());
#endif

    // Inner most loop, insert ULI polling.
    BasicBlock *HeaderBlock = CurrentLoop->getHeader();
#if 0
    BasicBlock *Latch = CurrentLoop->getLoopLatch();
    errs() << "Loop latch in Clone.cpp\n";
    if(Latch) {
      errs() << "Loop latch name: " << Latch->getName() << "\n";
      if(F->getFnAttribute("poll-at-loop").getValueAsString()=="true") {
        auto splitPt = Latch->getTerminator()->getPrevNode();
        auto afterBB = Latch->splitBasicBlock(splitPt);

        Instruction *term = Latch->getTerminator();
        //B.SetInsertPoint(term);
        B.SetInsertPoint(Latch->getTerminator());

        Value* bHaveUnwind = B.CreateLoad(Type::getInt1Ty(C), bHaveUnwindAlloc, 1);
        Value* haveBeenUnwind = B.CreateICmpEQ(bHaveUnwind, B.getInt1(1));
        BasicBlock* loopUnwound = BasicBlock::Create(C, "loop.unwounded", F);
        B.CreateCondBr(haveBeenUnwind, loopUnwound, afterBB);
        term->eraseFromParent();
        B.SetInsertPoint(loopUnwound);
        B.CreateRetVoid();
      }
    }
#endif

    if (HeaderBlock) {
      // If this a parallel-for-seq, insert a condition to terminate
      if(F->getFnAttribute("poll-at-loop").getValueAsString()=="true") {
#ifdef UI_REGION
	// Currently not in used
	Instruction* splitPt = nullptr;
        for( auto &BB : *F ) {
          for (auto &II : BB ) {
            if (IntrinsicInst *IntrinsicI = dyn_cast<IntrinsicInst>(&II)) {
              if (Intrinsic::ui_disable_region == IntrinsicI->getIntrinsicID()){
                splitPt = &II;
              }
            }
          }
        }
        auto afterBB = HeaderBlock->splitBasicBlock(splitPt->getNextNode());
#else
        auto splitPt = HeaderBlock->getFirstNonPHIOrDbgOrLifetime();
        auto afterBB = HeaderBlock->splitBasicBlock(splitPt);
#endif

        Instruction *term = HeaderBlock->getTerminator();
#ifdef PRL_LATER
	B.SetInsertPoint(term);
#else
	B.SetInsertPoint(HeaderBlock->getFirstNonPHIOrDbgOrLifetime());
#endif


#ifdef NO_UNWIND_POLLPFOR

	// TODO: CNP Check if return address is still the same
#ifdef PRL_LATER
	Value* myRAVal = B.CreateLoad(IntegerType::getInt64Ty(C), myRAStorage, 1);
	auto myCurrentRA = B.CreateCall(addrOfRA);
	myCurrentRA->setCanReturnTwice();
	auto myCurrentRAVal = B.CreateBitCast(myCurrentRA, IntegerType::getInt64Ty(C)->getPointerTo());
	myCurrentRAVal = B.CreateLoad(IntegerType::getInt64Ty(C), myCurrentRAVal, 1);
	Value* haveBeenUnwind = B.CreateICmpNE(myRAVal, myCurrentRAVal);
#else
	// Check if parallelism have been realized by using the value from bHaveUnwindAlloc
        Value* bHaveUnwind = B.CreateLoad(Type::getInt1Ty(C), bHaveUnwindAlloc, 1);
        Value* haveBeenUnwind = B.CreateICmpEQ(bHaveUnwind, B.getInt1(1));
#endif

	// If parallelism have been realized, return to parent
	BasicBlock* loopUnwound = BasicBlock::Create(C, "loop.unwounded", F);
        B.CreateCondBr(haveBeenUnwind, loopUnwound, afterBB);
        term->eraseFromParent();
        B.SetInsertPoint(loopUnwound);
        B.CreateRetVoid();
#else

        // No need for this if using unwind-ulifsim-poll

#endif

      }

#ifdef NO_UNWIND_POLLPFOR
      B.SetInsertPoint(HeaderBlock->getFirstNonPHIOrDbgOrLifetime());
      Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::uli_unwind_poll);
      B.CreateCall(pollFcn);
#endif

      LLVM_DEBUG(dbgs() << F->getName() << ": Polling at inner most loop\n");
    }


  }


  // Insert polling at the loop
  void insertPollingAtLoop(Loop &L, BasicBlock* unwindPathEntry, Value* bHaveUnwindAlloc) {
    SmallVector<Loop *, 8> VisitStack = {&L};
    Function *F = unwindPathEntry->getParent();

    // If -fpfor-spawn-strategy=2 or if it is a parallel-for
    if(EnableProperPolling == 2 || F->getFnAttribute("poll-at-loop").getValueAsString()=="true")
      instrumentLoop(F, &L, bHaveUnwindAlloc);

    while (!VisitStack.empty()) {
      Loop *CurrentLoop = VisitStack.pop_back_val();
      auto &SubLoops    = CurrentLoop->getSubLoops();

      if (!SubLoops.empty()) {
#if 1
        for (Loop *SubLoop : SubLoops)
          VisitStack.push_back(SubLoop);
#endif
      } else {
	// If -fpfor-spawn-strategy=3
        if(EnableProperPolling == 3)
          instrumentLoop(F, CurrentLoop, bHaveUnwindAlloc);
      }
    }
  }

}

namespace {
  struct LazyDTrans : public FunctionPass {
  public:
    static char ID;
    explicit LazyDTrans() : FunctionPass(ID) { initializeLazyDTransPass(*PassRegistry::getPassRegistry()); }
    //~LazyDTrans() { }

    // We don't modify the program, so we preserve all analyses
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      //Impl.runAnalysisUsage(AU);
      AU.addRequired<LoopInfoWrapperPass>();
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<DominanceFrontierWrapperPass>();
    }

    StringRef getPassName() const override {
      return "Simple Lowering of Tapir to LazyD ABI";
    }

    // Do some initialization
    virtual bool doInitialization(Module &M) override {
      return Impl.runInitialization(M);
    }

    bool runOnFunction(Function &F) override {
      FunctionAnalysisManager AM;

      auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
      auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
      auto &DF = getAnalysis<DominanceFrontierWrapperPass>().getDominanceFrontier();

      doInitialization(*F.getParent());

      return Impl.runImpl(F, AM, DT, DF, LI);
    }

  private:
    LazyDTransPass Impl;


  };
}

// LLVM uses the address of this static member to identify the pass, so the
// initialization value is unimportant.
char LazyDTrans::ID = 0;
INITIALIZE_PASS_BEGIN(LazyDTrans, "LazyDTrans",
                      "Lower Tapir to LazyDTrans", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass);
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominanceFrontierWrapperPass);
INITIALIZE_PASS_END(LazyDTrans, "LazyDTrans",
                    "Lower Tapir to LazyDTrans", false, false)

// Create the multiretcall from fast path to slow path
void LazyDTransPass::addPotentialJump(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder, ValueToValueMapTy& VMapSlowPath, Value* fromSlowPathAlloc, SSAUpdater& SSAUpdateWorkContext, DenseMap <DetachInst*, SmallPtrSet<AllocaInst*, 8>>& ReachingAllocSet, DominatorTree &DT) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::uli_potential_jump);
  IRBuilder<> B(C);

  // Type: void**
  // Use to materialiaze the work context that was obtained in the slow path entry
  SSAUpdateWorkContext.Initialize(IntegerType::getInt8Ty(C)->getPointerTo()->getPointerTo(), "workCtx");

  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  for (auto detachInst: bbOrder) {
    // Add  potential jump
    BasicBlock* pBB = detachInst->getParent();
    assert(pBB);
    BasicBlock* detachBB = detachInst->getDetached();

    detachBB = getBBContainReattached(detachBB);

    BasicBlock* continueBB  = detachInst->getContinue();
    SmallVector<Instruction *, 4> instsVec;
    for ( auto &II : *detachBB ) {
      instsVec.push_back(&II);
    }

    // --------------------------------------------------
    // Related to instrumentation for profiling
    SmallVector<Value*, 5> IntrinsicsArgs;
    // Look for Intrinsic::uli_lazyd_inst to clone
    for (auto &BB: F) {
      bool breakNow = false;
      for( auto &II : BB) {
	auto CI = dyn_cast<CallInst>(&II);
	Function *Intrinsic = nullptr;
	if(CI)  {
	  Intrinsic = CI->getCalledFunction();
	}
	if (Intrinsic && Intrinsic->getIntrinsicID() == Intrinsic::uli_lazyd_inst)
	  {

	    Constant *Message= dyn_cast<Constant>(CI->getArgOperand(1));
	    int messageVal = 0;
	    if(isa<ConstantExpr>(Message)) {
	      Instruction * i = (dyn_cast<ConstantExpr>(Message))->getAsInstruction();
	      if(i) {
		auto res = i->getOperand(0);
		if(isa<ConstantInt>(res))
		  messageVal = dyn_cast<ConstantInt>(res)->getSExtValue();
	      }
	    }

	    if(messageVal == 1) continue;

	    for(unsigned i=0; i<CI->arg_size(); i++) {
	      // Collect the arguments
	      IntrinsicsArgs.push_back(CI->getArgOperand(i));
	    }
	    breakNow = true;
	    break;
	  }
      }
      if (breakNow)
	break;
    }
    //---------------------------------------


    // Look for the spawn function
    for (auto ii : instsVec) {
      LLVM_DEBUG(dbgs() << "II: " << *ii << "\n");
      if ((isa<CallInst>(ii) || isa<InvokeInst>(ii)) && isNonPHIOrDbgOrLifetime(ii) ) {
        // Add a potential jump to slow path
	BasicBlock * continueSlowPathBB = dyn_cast<BasicBlock>(VMapSlowPath[continueBB]);

	// Replace call with multiretcall
	assert(isa<CallInst>(ii) && "Only supporting call instruction for now");
	auto mrc = replaceForkWithMultiRetCall(dyn_cast<CallInst>(ii), F);

	// Perform a branch to continueslowpath bb
	auto bb1 = mrc->getIndirectDest(0);
	B.SetInsertPoint(bb1);

	auto insertPt = dyn_cast<Instruction>(B.CreateBr(continueSlowPathBB));

	//------------------------------------------------------------------------------------
	// Used for profiling only
	if(IntrinsicsArgs.size() != 0) {
	  // Copy the uli_lazyd_inst in the
	  DT.recalculate(F);
	  // Look for uli_lazyd_inst and copy it to the slow path entry
	  Function* LazyDInstrumentation = Intrinsic::getDeclaration(M, Intrinsic::uli_lazyd_inst);
	  //B.SetInsertPoint(insertPt);

	  Instruction* insertPtOld = insertPt;

	  SmallVector<Value*, 5> Args;
	  for(int i=0; i<IntrinsicsArgs.size(); i++) {
	    Value* arg = nullptr;
	    if (i == 1) {
	      auto TWO = ConstantInt::get(IntegerType::getInt32Ty(C), 2, false);
	      auto TWOPTR = ConstantExpr::getIntToPtr(TWO, IntegerType::getInt8Ty(C)->getPointerTo(), false);
	      arg = TWOPTR;
	      //IntrinsicsArgs[i-1];
	    } else {
	      arg = IntrinsicsArgs[i];
	    }
	    if(!isa<Argument>(arg)) {
	      SmallVector<Instruction*, 8> Insts2Clone;
	      SmallSet<Value*, 4> dsts;
	      findRootArgument(arg, DT, insertPt, dsts);

	      // Have a for loop that loops the dst
	      if(dsts.size() > 0) {
		for(auto dst : dsts) {
		  SmallSet<Instruction*, 8> InstsSet;
		  findPathToDst(arg, dst, Insts2Clone, InstsSet);
		  if (Insts2Clone.size() == 0)
		    Args.push_back(dst);
		}
	      } else {
		Args.push_back(arg);
	      }

	      // Insert the cloned instruction
	      ValueToValueMapTy VMapClone;
	      if(Insts2Clone.size() > 0) {
		int i=0;
		for(auto ii: Insts2Clone) {
		  // If the instruction already dominate insertPt, then there is no need to clone, and just break
		  if(DT.dominates(ii, insertPtOld)) {
		    if(i == 0)
		      Args.push_back(ii);
		    continue;
		  }

		  Instruction * iiClone = ii->clone();
		  iiClone->insertBefore(insertPt);
		  VMapClone[ii] = iiClone;
		  insertPt = iiClone;
		  if(i == 0)
		    Args.push_back(iiClone);
		  i++;
		}
		//insertPt = dyn_cast<Instruction>(VMapClone[Insts2Clone[0]]);
		insertPt = insertPtOld;
	      }
	      // Update the use def of the cloned instruction
	      SmallVector< Use*, 4 >  useNeed2Update;
	      for(auto ii: Insts2Clone) {
		useNeed2Update.clear();
		if(!VMapClone[ii]) {
		  continue;
		}

		Instruction * clonedII = dyn_cast<Instruction>(VMapClone[ii]);

		for (auto &use : ii->uses()) {
		  auto * user = dyn_cast<Instruction>(use.getUser());
		  if(user->getParent() == insertPt->getParent()) {
		    useNeed2Update.push_back(&use);
		  }
		}
		for( auto U : useNeed2Update ){
		  U->set(clonedII);
		}

		// If it is a phi node, change the predecessor to the precedecessor of the slowpathentry
		if(isa<PHINode>(clonedII)) {
		  PHINode* phiNode = dyn_cast<PHINode>(clonedII);
		  if(phiNode->getNumIncomingValues() == 1) {
		    // If only have one predecessor
		    phiNode->replaceIncomingBlockWith(phiNode->getIncomingBlock(0), detachInst->getDetached());
		  } else {
		    // If only have two or more predecessor
		    // Delete value not from the same basic block
		    unsigned incomingPair = phiNode->getNumIncomingValues();
		    for(unsigned i = 0; i<incomingPair; i++)  {
		      //Instruction* incomingVal = dyn_cast<Instruction>(phiNode->getIncomingValue(i));
		      auto incomingVal = (phiNode->getIncomingValue(i));
		      if(!DT.dominates(incomingVal, clonedII)) {
			// Remove the incoming block and its value
		      } else {
		      }
		    }
		    phiNode->replaceIncomingBlockWith(phiNode->getIncomingBlock(0), detachInst->getDetached());
		  }
		}
	      }

	    } else {
	      Args.push_back(arg);
	    }
	  }
	  B.SetInsertPoint(insertPt->getParent()->getTerminator());
	  auto res = B.CreateCall(LazyDInstrumentation, Args);
	  if(res->getPrevNode())
	    res->setDebugLoc(res->getPrevNode()->getDebugLoc());
	  else
	    res->setDebugLoc(detachInst->getDebugLoc());
	}
      }
      //------------------------------------------------------------------------------------
    }
  }
  return;
}

// Current not used.
// Insert a check in the continuation block.
void LazyDTransPass::insertCheckInContBlock(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder, ValueToValueMapTy& VMapSlowPath, Value* fromSlowPathAlloc,
                            DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB, SSAUpdater& SSAUpdateWorkContext) {

  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::uli_potential_jump);
  IRBuilder<> B(C);

  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  for (auto detachInst: bbOrder) {
    // Ignore detach that do not have any reaching detaches (since these detaches do not exist in the slow path)
    if(RDIBB[detachInst].empty()) continue;


    BasicBlock* pBB = detachInst->getParent();
    assert(pBB);

    auto detachParent = detachInst->getParent();
    BasicBlock * detachParentSlowPathBB = dyn_cast<BasicBlock>(VMapSlowPath[detachParent]);

    DetachInst* detachInstSlowPath = dyn_cast<DetachInst>(detachParentSlowPathBB->getTerminator());

    // Store one to fromSlowPathAlloc before the detachInstSlowPath
    B.SetInsertPoint(detachInstSlowPath);
    B.CreateAlignedStore(B.getInt32(0), fromSlowPathAlloc, Align(4), 1);

    // Get the slow path continuation
    BasicBlock* continueBBSlowPath  = detachInstSlowPath->getContinue();

    // Split the basic block
    auto insertPt = continueBBSlowPath->getFirstNonPHIOrDbgOrLifetime();
    B.SetInsertPoint(insertPt);

    auto fromSlowPath = B.CreateAlignedLoad(Type::getInt8Ty(C), fromSlowPathAlloc, Align(4), 1);
    auto isFromSlowPath = B.CreateICmpEQ(fromSlowPath, B.getInt32(1), "isFromSlowPath");

    auto splitPt = dyn_cast<Instruction>(isFromSlowPath)->getNextNode();
    auto afterBB = continueBBSlowPath->splitBasicBlock(splitPt);


    BasicBlock* reloadWorkCtxBB = BasicBlock::Create(C, "reloadWorkCtxBB", &F);
    B.SetInsertPoint(reloadWorkCtxBB);

    Function* uliGetWorkCtx = Intrinsic::getDeclaration(M, Intrinsic::uli_get_workcontext);
    //uliGetWorkCtx->addFnAttr(Attribute::Forkable);
    auto workCtx = B.CreateCall(uliGetWorkCtx);
    //workCtx->setTailCall(true);
    B.CreateAlignedStore(B.getInt32(1), fromSlowPathAlloc, Align(4), 1);
    B.CreateBr(afterBB);

    auto branch = BranchInst::Create(afterBB, reloadWorkCtxBB, isFromSlowPath);
    //auto branch = BranchInst::Create(afterBB);
    ReplaceInstWithInst(continueBBSlowPath->getTerminator(), branch);

    SSAUpdateWorkContext.AddAvailableValue(reloadWorkCtxBB, workCtx);
  }

  return;
}


// Replace the uses of slowLiveVar with liveVar
void LazyDTransPass::replaceUses(Instruction *liveVar, Instruction *slowLiveVar) {
  SmallVector< Use*, 4 >  useNeed2Update;
  for (auto &use : slowLiveVar->uses()) {
    useNeed2Update.push_back(&use);
  }
  for( auto U : useNeed2Update ){
    U->set(liveVar);
  }
  return;
}

// Materialize/Use an instruction to replace inst2replace.
void LazyDTransPass::updateSSA(SSAUpdater& SSAUpdate, Instruction* inst2replace) {
  SmallVector<Use*, 16> UsesToRename;

  // Update phi node by adding incoming instruction from different basic block that is not in the phi node yet.
  for (Use &U : inst2replace->uses()) {
    Instruction *User = cast<Instruction>(U.getUser());
    if (PHINode *UserPN = dyn_cast<PHINode>(User)) {
      BasicBlock* currBB = UserPN->getParent();
      DenseMap <PHINode*, std::pair<Value*, BasicBlock*>> phiNode2Update;
      // Iterate the predecessor of the basic block
      for( pred_iterator PI = pred_begin(currBB); PI != pred_end(currBB); PI++ ) {
        BasicBlock* pred = *PI;
        unsigned incomingPair = UserPN->getNumIncomingValues();
        bool foundPair = false;

	// Check if the predecessor is part of the Phi Node.
	// Bad approach, can be done in better way similar to merge in mergesort
        for(unsigned i = 0; i<incomingPair; i++)  {
          auto bb = dyn_cast<BasicBlock>(UserPN->getIncomingBlock(i));
          if(bb == pred) {
            foundPair = true;
            break;
          }
        }
	// Check if predecessor not part of the phi node.
        if(!foundPair) {
          Value* rematerialzeVal = nullptr;
          if(true)
            // Needed for cholesky
            rematerialzeVal = SSAUpdate.GetValueAtEndOfBlock(pred);
          else
            rematerialzeVal = SSAUpdate.GetValueInMiddleOfBlock(pred);
          phiNode2Update[UserPN]  = std::pair<Value*, BasicBlock*>(rematerialzeVal, pred);
        }
      }

      // Update phi node with new predecessor
      for(auto elem: phiNode2Update) {
        PHINode* phiNode = elem.first;
        phiNode->addIncoming(elem.second.first, elem.second.second);
      }
    }
  }

  // Update inst2replace user who are not in the same basic block or an incoming value in the same basic block
  for (Use &U : inst2replace->uses()) {
    Instruction *User = cast<Instruction>(U.getUser());
    if (PHINode *UserPN = dyn_cast<PHINode>(User)) {
      // Incoming basic block that has the same basic block with inst2replace
      if (UserPN->getIncomingBlock(U) == inst2replace->getParent()) {
        continue;
      }

    } else if (User->getParent() == inst2replace->getParent()) {
      // User have the same parent with inst2replace
      continue;
    }
    UsesToRename.push_back(&U);
  }

  // Update the uses with SSAUpdate
  while (!UsesToRename.empty()) {
    auto use = UsesToRename.pop_back_val();
    Instruction *User = cast<Instruction>(use->getUser());
    SSAUpdate.RewriteUse(*use);
    //SSAUpdate.RewriteUseAfterInsertions(*use);
  }
}

// For instruction in the fast path that always dominate the slow path (does not need a slow path),
// replace the use of the slow path inst version with the one from the fast path
void LazyDTransPass::updateSlowVariables_2(Function& F,
                           ValueToValueMapTy& VMapSlowPathReverse, ValueToValueMapTy& VMapSlowPath,
                           DenseMap<BasicBlock*, BasicBlock*> syncBB2syncPred,
                           DominatorTree &DT, DominanceFrontier &DF,
                           DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap,
                           SmallPtrSet<Instruction*, 8>& RequiredPhiNode,
                           SmallPtrSet<Instruction*, 8>& PhiNodeInserted,
                           DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                           SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,
                           SmallVector<SyncInst*, 8>& syncInsts  ) {

  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  // Loop over the detach's parent
  for (auto detachInst: bbOrder) {
    BasicBlock* pBB = detachInst->getParent();
    assert(pBB);
    BasicBlock* parent = detachInst->getParent();
    BasicBlock* continueBB  = detachInst->getContinue();
    BasicBlock* slowContinueBB = dyn_cast<BasicBlock>(VMapSlowPath[continueBB]);

    // For live instruction not in required phi node, replace all uses
    auto liveVariableInBB = LVin[continueBB];
    for (auto elem2 : liveVariableInBB) {
      BasicBlock * bbPred = elem2.first;
      // Get live variable in from actual parent
      if (bbPred == parent) {
        for(auto val : elem2.second) {
          Instruction * liveVar = dyn_cast<Instruction>(val);

          if(!VMapSlowPath[liveVar])
            continue;

          Instruction * slowLiveVar = dyn_cast<Instruction>(VMapSlowPath[liveVar]);
          auto requiredPhiVarSet = RequiredPhiNode;
          // Already modified
          if(PhiNodeInserted.find(liveVar) != PhiNodeInserted.end())
            continue;

          PhiNodeInserted.insert(liveVar);

          if(requiredPhiVarSet.find(liveVar) == requiredPhiVarSet.end()){
            // Replace the instruction in slow path with fast path since it dominates all path
            replaceUses(liveVar, slowLiveVar);
          } else {
            if(liveVar->getType()->isTokenTy())
              continue;

            SSAUpdater SSAUpdate;
            SSAUpdate.Initialize(slowLiveVar->getType(), slowLiveVar->getName());
            SSAUpdate.AddAvailableValue(liveVar->getParent(), liveVar);
            SSAUpdate.AddAvailableValue(slowLiveVar->getParent(), slowLiveVar);

            updateSSA(SSAUpdate, slowLiveVar);
            updateSSA(SSAUpdate, liveVar);
          }
        }
      } // End if bbPred == parent
    }
  }

  // FIXME:Add a check to see if the live variable is not defined inside the parallel region.
  // If not defined, the edge from the slow path is the same from the fast path.
  // Will still need to rematerialize (using SSAUpdate), incase the sync in the fast path has two predecessor.
  // Only that the data from the slow path uses the data from the fast path.

  DenseMap<Instruction*, bool> AlreadyAnalyzed;
  for(auto syncInst: syncInsts) {
    BasicBlock* pBB = syncInst->getParent();
    assert(pBB);
    BasicBlock* parent = syncInst->getParent();
    BasicBlock* continueBB  = syncInst->getSuccessor(0);
    BasicBlock* slowContinueBB = dyn_cast<BasicBlock>(VMapSlowPath[continueBB]);
    // For live instruction not in required phi node, replace all uses
    auto liveVariableInBB = LVin[continueBB];

    for (auto elem2 : liveVariableInBB) {
      BasicBlock * bbPred = elem2.first;
      // Get live variable in from actual parent
      if (bbPred == pBB) {
        for(auto val : elem2.second) {
          Instruction * liveVar = dyn_cast<Instruction>(val);
          auto slowLiveVarVal = (VMapSlowPath[liveVar]);
          DenseMap <PHINode*, std::pair<Value*, BasicBlock*>> phiNode2Update;
          if(slowLiveVarVal) {
            // If liveVar is used in a phi node in the fast path, make sure to update the incoming edge from the slow path
            // Since there is only one entry point, look for the other variable, rematerialze it in the preSync
            // Update the phi node

            SSAUpdater SSAUpdate;

            // Reinitialize SSAUpdate
            SSAUpdate.Initialize(liveVar->getType(), liveVar->getName());

            for (Use &U : liveVar->uses()) {
              Instruction *User = cast<Instruction>(U.getUser());
              if (PHINode *phiInst = dyn_cast<PHINode>(User)) {
                if(phiInst->getParent() != continueBB) continue;

                if(AlreadyAnalyzed.count(phiInst)) {
                  continue;
                }
                AlreadyAnalyzed[phiInst]=true;

                // Get all the incoming variable
                unsigned incomingPair = phiInst->getNumIncomingValues();

                // If phi node after sync already have incoming variable from slow path, then ignore.
                // TODO: CNP why is this needed for usingt the new clang++
                bool bCont = false;
                for(unsigned i = 0; i<incomingPair; i++)  {
                  BasicBlock* incomingBB = phiInst->getIncomingBlock(i);
                  Instruction* incomingInst = dyn_cast<Instruction>(phiInst->getIncomingValue(i));
                  // If incoming BB already from pre.sync? But how?
                  if(incomingBB  == syncBB2syncPred[continueBB])
                    bCont = true;
                }
                if(bCont)
                  continue;


                for(unsigned i = 0; i<incomingPair; i++)  {
                  BasicBlock* incomingBB = phiInst->getIncomingBlock(i);
                  Instruction* incomingInst = dyn_cast<Instruction>(phiInst->getIncomingValue(i));

                  // if incoming inst is not part of the paralell region
                  if(incomingInst != liveVar)
                    continue;

                  // If incoming inst is an argument
                  if(!incomingInst) {
                    SSAUpdate.AddAvailableValue(incomingBB, phiInst->getIncomingValue(i));
                    continue;
                  }
                  // TODO: CNP
                  // In LU
                  // %cmp.i.slowPath148 = phi i1 [ %cmp.i.slowPath149, %pre.sync ], [ %cmp.i, %det.cont.i ], [ %cmp.i, %if.then.i ]
                  // After changes
                  //%cmp.i.slowPath148 = phi i1 [ %cmp.i.slowPath149, %pre.sync ], [ %cmp.i, %det.cont.i ], [ %cmp.i, %if.then.i ], [ %cmp.i159, %pre.sync ]
                  // Where do cmp.i.slowPath149 comes from?
                  // Which value in pre.sync should i use, cmp.i.slowpath149 or cmp.i159
                  if(!VMapSlowPath[incomingInst])
                    continue;

                  auto incomingInstSlow = dyn_cast<Instruction>(VMapSlowPath[incomingInst]);
                  if(!incomingInstSlow)
                    continue;

                  auto requiredPhiVarSet = RequiredPhiNode;

                  // If incoming inst dominate parallel region,
                  // then add value where the source is from slow path to fast path
                  if(requiredPhiVarSet.find(incomingInst) == requiredPhiVarSet.end()) {
                    SSAUpdate.AddAvailableValue(syncBB2syncPred[continueBB], incomingInst);
                    continue;
                  }

                  // For phi node with incoming value a constant from parallel region, create one for the slow path as well.
                  auto incomingConstant = dyn_cast<Constant>(phiInst->getIncomingValue(i));
                  if(incomingConstant) {
                    // If coming from parallel region, use SSA updater
                    SSAUpdate.AddAvailableValue(dyn_cast<BasicBlock>(VMapSlowPath[phiInst->getIncomingBlock(i)]), incomingConstant);
                    continue;
                  }
                  SSAUpdate.AddAvailableValue(incomingInstSlow->getParent(), incomingInstSlow);
                }
                // TODO: When to use which one?
                Value* rematerialzeVal = nullptr;
                if(true)
                  // Needed for cholesky
                  rematerialzeVal = SSAUpdate.GetValueAtEndOfBlock(syncBB2syncPred[continueBB]);
                else
                  rematerialzeVal = SSAUpdate.GetValueInMiddleOfBlock(syncBB2syncPred[continueBB]);

                phiNode2Update[phiInst]  = std::pair<Value*, BasicBlock*>(rematerialzeVal, syncBB2syncPred[continueBB]);
              }
            }

            for(auto elem: phiNode2Update) {
              PHINode* phiNode = elem.first;
              phiNode->addIncoming(elem.second.first, elem.second.second);
            }
          }
        }
      }
    }
  }

  // Loop over the sync's parent. Only update non-phinode uses
  for (auto syncInst: syncInsts) {
    BasicBlock* pBB = syncInst->getParent();
    assert(pBB);
    BasicBlock* parent = syncInst->getParent();
    BasicBlock* continueBB  = syncInst->getSuccessor(0);
    BasicBlock* slowContinueBB = dyn_cast<BasicBlock>(VMapSlowPath[continueBB]);

    // For live instruction not in required phi node, replace all uses
    auto liveVariableInBB = LVin[continueBB];
    for (auto elem2 : liveVariableInBB) {
      BasicBlock * bbPred = elem2.first;
      // Get live variable in from actual parent
      if (bbPred == parent) {
        for(auto val : elem2.second) {
          Instruction * liveVar = dyn_cast<Instruction>(val);

          // Already modified
          if(!VMapSlowPath[liveVar])
            continue;

          Instruction * slowLiveVar = dyn_cast<Instruction>(VMapSlowPath[liveVar]);
          auto requiredPhiVarSet = RequiredPhiNode;
          if(PhiNodeInserted.find(liveVar) != PhiNodeInserted.end()) {
            continue;
          }
          PhiNodeInserted.insert(liveVar);

          if(requiredPhiVarSet.find(liveVar) == requiredPhiVarSet.end()){
            // Replace the instruction in slow path with fast path since it dominates all path
            replaceUses(liveVar, slowLiveVar);
          } else {
            if(liveVar->getType()->isTokenTy())
              continue;

            SSAUpdater SSAUpdate;
            SSAUpdate.Initialize(slowLiveVar->getType(), slowLiveVar->getName());
            SSAUpdate.AddAvailableValue(liveVar->getParent(), liveVar);
            SSAUpdate.AddAvailableValue(slowLiveVar->getParent(), slowLiveVar);

            updateSSA(SSAUpdate, slowLiveVar);
            updateSSA(SSAUpdate, liveVar);
          }
        }
      } // End if bbPred == parent
    }
  }

  // For phi node with incoming value a constant from parallel region, create one for the slow path as well.
  for (auto syncInst: syncInsts) {
    BasicBlock* pBB = syncInst->getParent();
    assert(pBB);
    BasicBlock* parent = syncInst->getParent();
    BasicBlock* continueBB  = syncInst->getSuccessor(0);
    BasicBlock* slowContinueBB = dyn_cast<BasicBlock>(VMapSlowPath[continueBB]);

    for (auto &II : *continueBB ) {
      // If phi Inst has a constant
      if (PHINode *phiInst = dyn_cast<PHINode>(&II)) {

        if(AlreadyAnalyzed.count(phiInst)) {
          continue;
        }
        AlreadyAnalyzed[phiInst]=true;

        unsigned incomingPair = phiInst->getNumIncomingValues();

        SSAUpdater SSAUpdate;
        SSAUpdate.Initialize(phiInst->getType(), phiInst->getName());

        bool needUpdate = false;
        for(unsigned i = 0; i<incomingPair; i++)  {
          auto incomingConstant = dyn_cast<Constant>(phiInst->getIncomingValue(i));

          if(incomingConstant) {
            needUpdate = true;
            // If coming from parallel region, use SSA updater
            SSAUpdate.AddAvailableValue(dyn_cast<BasicBlock>(VMapSlowPath[phiInst->getIncomingBlock(i)]), incomingConstant);
          }
        }

        if(needUpdate) {
          // Update phi Node
          auto rematerialzeVal = SSAUpdate.GetValueAtEndOfBlock(syncBB2syncPred[continueBB]);
          phiInst->addIncoming(rematerialzeVal, syncBB2syncPred[continueBB]);
        }
      }
    }
  }
  return;
}

// If a variable is located in the parallel path, then it needs a phi node
void LazyDTransPass::findRequiredPhiNodes(DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIPath,
                          DenseMap<SyncInst *, SmallPtrSet<BasicBlock*, 8>>& RSIPath,
                          DenseMap<BasicBlock*, BitVector> &MapBB2InVal,
                          DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                          SmallVector<SyncInst*, 8>& syncInsts,
                          SmallPtrSet<Instruction*, 8>& RequiredPhiNode) {


  // Iterate over the detach inst
  for(auto elem: RDIPath) {
    DetachInst * DI = elem.first;
    BasicBlock * parent = DI->getParent();
    BasicBlock * continuation = DI->getContinue();
    // Get the live IN variable in the continue path
    auto liveVariableInBB = LVin[continuation];
    // Get any basic block from a detach point that can reach this continuation
    for (auto elem2 : liveVariableInBB) {
      BasicBlock * bbPred = elem2.first;
      // If live in coming from the detach instruction parent and not the detached basic block.
      // Remember that the continuation has two predecessor: detached block and the detach inst's parent.
      if (bbPred == parent) {
        for(auto val : elem2.second) {
          Instruction * liveVar = dyn_cast<Instruction>(val);
          BasicBlock * livebb = liveVar->getParent();
	  //  A detach inst can reach this liveVar without going through a sync, hence it is part of a parallel path
          if(!MapBB2InVal[livebb].none()){
            RequiredPhiNode.insert(liveVar);
          }
        }
      }
    }
  }

  // Similar logic with the above code but is for sync inst
  // Can be refactor as a function.
  for(auto elem: RSIPath) {
    SyncInst * SI = elem.first;
    BasicBlock * parent = SI->getParent();
    auto syncSucc = SI->getSuccessor(0);
    // Another difference is that is has to be live in to the successor of the sync
    auto liveVariableInBB = LVin[syncSucc];
    // Get any basic block from a detach point that can reach this continuation
    for (auto elem2 : liveVariableInBB) {
      BasicBlock * bbPred = elem2.first;
      if (bbPred == parent) {
        for(auto val : elem2.second) {
          Instruction * liveVar = dyn_cast<Instruction>(val);
          BasicBlock * livebb = liveVar->getParent();
          if(!MapBB2InVal[livebb].none()){
            RequiredPhiNode.insert(liveVar);
          }
        }
      }
    }
  }

#if 0
  // Debugging purpose
  for(auto elem : RequiredPhiNode) {
    LLVM_DEBUG(dbgs() << "Detach Inst : " << *(elem.first) <<"\n");
    for (auto inst : elem.second) {
      LLVM_DEBUG(dbgs() << "Required phi " << *inst <<"\n");
    }
    LLVM_DEBUG(dbgs() << "-------------------\n");
  }
#endif
  return;
}


// Call the simpluyf CFG
void LazyDTransPass::simplifyFcn(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT) {
  const SimplifyCFGOptions Options;
#if 1
  DomTreeUpdater DTU(DT, DomTreeUpdater::UpdateStrategy::Eager);

  auto *TTI = &AM.getResult<TargetIRAnalysis>(F);
  SmallVector<BasicBlock*, 8> bbInF;
  bbInF.clear();
  for( auto &BB : F ) {
    bbInF.push_back(&BB);
  }

  for (auto pBB : bbInF) {
    simplifyCFG(pBB, *TTI, nullptr, Options);
  }
#endif
  return;
}

/// Replace the use of result from a fork call with the retpad.
void LazyDTransPass::replaceResultOfMultiRetCallWithRetpad(Function &F) {
  for( auto &BB : F ) {
    for (auto &II : BB ) {

      // Look for multiretcall that is not of void type
      if(isa<MultiRetCallInst>(&II) && !(dyn_cast<MultiRetCallInst>(&II)->getFunctionType()->getReturnType()->isVoidTy()) ) {
        auto mrc = dyn_cast<MultiRetCallInst>(&II);

        // Get all the retpad
        SmallVector<RetPadInst *, 4> retPadInsts;

	// One from indirectBB
        for(auto indirectBB: mrc->getIndirectDests()) {
          for(auto &ii : *indirectBB) {
            if(isa<RetPadInst>(&ii)) {
              retPadInsts.push_back(dyn_cast<RetPadInst>(&ii));
            }
          }
        }
	// One from default dest
        auto bb0 = mrc->getDefaultDest();
        for(auto &ii : *bb0){
          if(isa<RetPadInst>(&ii)) {
            retPadInsts.push_back(dyn_cast<RetPadInst>(&ii));
          }
        }

	// Use SSAUpdate to update return result of fork with retpad
        SmallVector<Use*, 16> UsesToRename;
        SSAUpdater SSAUpdate;
        SSAUpdate.Initialize(mrc->getType(), mrc->getName());

	// Update SSA with the avialable value
        for(auto ri: retPadInsts) {
          SSAUpdate.AddAvailableValue(ri->getParent(), ri);
        }

        // Rename the uses of the result of fork
        for (Use &U : mrc->uses()) {
          Instruction *User = cast<Instruction>(U.getUser());
	  // Don't update uses that belong to same basic block, is already a retpad, an immediate phi node usage
          if (PHINode *UserPN = dyn_cast<PHINode>(User)) {
            if (UserPN->getIncomingBlock(U) == mrc->getParent()) {
              continue;
            }
          } else if(isa<RetPadInst>(User) || (User->getParent() == mrc->getParent()) ) {
            continue;
          }
	  // The rest, save it in usestorename
          UsesToRename.push_back(&U);
        }

	// Update the uses with reptad
        while (!UsesToRename.empty())
          SSAUpdate.RewriteUseAfterInsertions(*UsesToRename.pop_back_val());
      }
    }
  }
  return;
}

// Clone BasicBlock
// If load and store is from the slow path, set it to volatile
void LazyDTransPass::cloneBasicBlock(Function &F, SmallVector<BasicBlock*, 8>& bb2clones, ValueToValueMapTy& VMapSlowPath, ValueToValueMapTy& VMapSlowPathReverse,
                     SmallPtrSet<AllocaInst*, 8>& AllocaSet ) {
  DebugInfoFinder DIFinder;
  DISubprogram *SP = F.getSubprogram();
  if (SP) {
    // Add mappings for some DebugInfo nodes that we don't want duplicated
    // even if they're distinct.
    auto &MD = VMapSlowPath.MD();
    MD[SP->getUnit()].reset(SP->getUnit());
    MD[SP->getType()].reset(SP->getType());
    MD[SP->getFile()].reset(SP->getFile());
    MD[SP].reset(SP);
  }

  // Perform the actual cloning
  for (auto pBB : bb2clones){
    VMapSlowPath[pBB] = CloneBasicBlock(pBB, VMapSlowPath, ".slowPath", &F, nullptr, &DIFinder);
    VMapSlowPathReverse[VMapSlowPath[pBB]] = pBB;
  }

  // --------------------------------------------------------------

  for(auto pBB : bb2clones) {
    BasicBlock * ClonedBB = dyn_cast<BasicBlock>(VMapSlowPath[pBB]);

    // TODO: Is this needed when we merge back the path
    // Since the slow path RSP's might be different from the fast path's, restore fast path's rsp using the fast path's base pointer (which is the same with slow path's base pointer)
    IRBuilder<> B(F.getContext());
    Instruction * termInst = ClonedBB->getTerminator();
    if(isa<ReturnInst>(termInst) ){
      B.SetInsertPoint(termInst);
      // If there is only dynamic alloca
#ifdef OPTIMIZE_FP
    if(bHaveFork || bHaveCallFcn6Args) {
#else
    if(true) {
#endif
        Function *SetupRSPfromRBP = Intrinsic::getDeclaration(F.getParent(), Intrinsic::setup_rsp_from_rbp);
        B.CreateCall(SetupRSPfromRBP);
      }
    }

    for (Instruction &II : *ClonedBB) {
      // Look for the store inst and load inst in the slow path that uses the alloca
      // for fork result. Set it then to volatile
      if(isa<StoreInst>(&II)) {
        StoreInst* si = dyn_cast<StoreInst> (&II);
        Instruction* siPtr = dyn_cast<Instruction>(si->getPointerOperand());
        if(siPtr) {
          AllocaInst* ai = dyn_cast<AllocaInst>(siPtr);

          if(ai && AllocaSet.find(ai) != AllocaSet.end()) {
            // If the pointer operand is a fork storage
            si->setVolatile(true);
          } else {
            // If the definition uses one of the alloca variable
            unsigned nOp = siPtr->getNumOperands();
            for (unsigned i = 0; i<nOp; i++) {
              auto opVal = siPtr->getOperand(i);
              AllocaInst* ai2 = dyn_cast<AllocaInst>(opVal);
              if(ai2 && AllocaSet.find(ai2) != AllocaSet.end()) {
                // If the pointer operand uses the fork storage
                si->setVolatile(true);
              }
            }
          }
        }
      } else if (isa<LoadInst>(&II)) {
        // Similarly for fork storage
        LoadInst* li = dyn_cast<LoadInst> (&II);
        Instruction* liPtr = dyn_cast<Instruction>(li->getPointerOperand());
        if(liPtr) {
          AllocaInst* ai = dyn_cast<AllocaInst>(liPtr);

          if(ai && AllocaSet.find(ai) != AllocaSet.end()) {
            li->setVolatile(true);
          } else {
            // If the definition uses one of the alloca variable
            unsigned nOp = liPtr->getNumOperands();
            for (unsigned i = 0; i<nOp; i++) {
              auto opVal = liPtr->getOperand(i);
              AllocaInst* ai2 = dyn_cast<AllocaInst>(opVal);
              if(ai2 && AllocaSet.find(ai2) != AllocaSet.end()) {
                li->setVolatile(true);
              }
            }
          }
        }
      }

      // Remap the cloned instruction
      auto remapFlag = RF_IgnoreMissingLocals | RF_ReuseAndMutateDistinctMDs;
      RemapInstruction(&II, VMapSlowPath, F.getSubprogram() != nullptr? RF_None | remapFlag  : RF_NoModuleLevelChanges | remapFlag, nullptr, nullptr);
    }
  }

  return;
}


void LazyDTransPass::postProcessCfg(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT, SmallPtrSet<AllocaInst*, 8>& AllocaSet) {
  // Desirable to  verify the IR before running simplify
  // Can this be commented out?
  simplifyFcn(F, AM, DT);

  // Make sure that the store and load to fork storage is volatile (not optimize out)
  for(auto ai : AllocaSet) {
    for (auto &use : ai->uses()) {
      auto * user = dyn_cast<Instruction>(use.getUser());
      if(!use) continue;
      if(isa<StoreInst>(user)  ) {
	StoreInst * si = dyn_cast<StoreInst>(user);
	si->setVolatile(true);
      } else if (isa<LoadInst>(user)) {
	LoadInst * li = dyn_cast<LoadInst>(user);
	li->setVolatile(true);
      }
    }
  }

  // Update the multiretcall inst with the retpad inst
  replaceResultOfMultiRetCallWithRetpad(F);

  // Desirable to  verify the IR before running simplify
  simplifyFcn(F, AM, DT);

  // Verify function
  if (verifyFunction(F, &errs())) {
    F.dump();
    llvm_unreachable("Tapir lowering produced bad IR!");
  }
  return;
}


/// Copied from CilkABI.cpp
/// \brief Lower a call to get the grainsize of this Tapir loop.
///
/// The grainsize is computed by the following equation:
///
///     Grainsize = min(2048, ceil(Limit / (8 * workers)))
///
/// This computation is inserted into the preheader of the loop.
Value* LazyDTransPass::lowerGrainsizeCall(CallInst *GrainsizeCall) {
  Value *Limit = GrainsizeCall->getArgOperand(0);
  Module *M = GrainsizeCall->getModule();
  IRBuilder<> Builder(GrainsizeCall);

  // Get 8 * workers
  Type *Int32Ty = Type::getInt32Ty(M->getContext());
  GlobalVariable* gCilkg_nproc = GetGlobalVariable("cilkg_nproc", Int32Ty, *M, false);
  Value* Workers = Builder.CreateLoad(Int32Ty, gCilkg_nproc);

  Value *WorkersX8 = Builder.CreateIntCast(
                                           Builder.CreateMul(Workers, ConstantInt::get(Workers->getType(), 8)),
                                           Limit->getType(), false);
  // Compute ceil(limit / 8 * workers) =
  //           (limit + 8 * workers - 1) / (8 * workers)
  Value *SmallLoopVal =
    Builder.CreateUDiv(Builder.CreateSub(Builder.CreateAdd(Limit, WorkersX8),
                                         ConstantInt::get(Limit->getType(), 1)),
                       WorkersX8);
  // Compute min
  Value *LargeLoopVal = ConstantInt::get(Limit->getType(), MaxGrainSize);
  Value *Cmp = Builder.CreateICmpULT(LargeLoopVal, SmallLoopVal);
  Value *Grainsize = Builder.CreateSelect(Cmp, LargeLoopVal, SmallLoopVal);



  // Replace uses of grainsize intrinsic call with this grainsize value.
  GrainsizeCall->replaceAllUsesWith(Grainsize);
  return Grainsize;
}

void LazyDTransPass::convertTapirIrToBr(Function &F) {
  DenseMap<Instruction*, Instruction*> replaceInstMap;
  for(auto &BB : F) {
    if(isa<DetachInst>(BB.getTerminator())) {
      DetachInst* detachInst = dyn_cast<DetachInst>(BB.getTerminator());
      BasicBlock* detachBB = detachInst->getDetached();
      BasicBlock* contBB = detachInst->getContinue();
      BranchInst* brInst = BranchInst::Create(detachBB);
      replaceInstMap[detachInst] = brInst;

      // Look for phi node in contBB, and remove any incoming value from BB(parent of detach inst)
      for(auto &ii: *contBB) {
        if(isa<PHINode>(&ii)){
          // Removie incoming value from continue
          SmallVector<BasicBlock*, 4> removeBBs;
          PHINode* phiN = dyn_cast<PHINode>(&ii);
          unsigned incomingPair = phiN->getNumIncomingValues();
          for(unsigned i = 0; i<incomingPair; i++)  {
            BasicBlock* incomingBB = phiN->getIncomingBlock(i);
            if ( incomingBB == &BB ) {
              removeBBs.push_back(&BB);
            }
          }
          for(auto bb: removeBBs) {
            phiN->removeIncomingValue(bb);
          }
        }
      }

    } else if (isa<ReattachInst>( BB.getTerminator() )) {
      ReattachInst* reattachInst = dyn_cast<ReattachInst>(BB.getTerminator());
      BasicBlock* contBB = reattachInst->getDetachContinue();
      BranchInst* brInst = BranchInst::Create(contBB);
      replaceInstMap[reattachInst] = brInst;

    } else if (isa<SyncInst>( BB.getTerminator() )) {
      SyncInst* syncInst = dyn_cast<SyncInst>(BB.getTerminator());
      BasicBlock* succ = syncInst->getSuccessor(0);
      BranchInst* brInst = BranchInst::Create(succ);
      replaceInstMap[syncInst] = brInst;
    }
  }

  for(auto elem : replaceInstMap) {
    ReplaceInstWithInst(elem.first, elem.second);
  }
  return;
}


BasicBlock* LazyDTransPass::createUnwindHandler(Function &F, Value* locAlloc, Value* ownerAlloc, Value* bHaveUnwindAlloc, SmallVector<DetachInst*, 4>& bbOrder, ValueToValueMapTy& VMapSlowPath, ValueToValueMapTy& VMapGotStolenPath) {
  Module* M = F.getParent();
  const DataLayout &DL = M->getDataLayout();
  LLVMContext& C = M->getContext();
  using addr_ty = void *;
  IRBuilder <> B(C);
  auto workcontext_ty = ArrayType::get(PointerType::getInt8PtrTy(C), WorkCtxLen);

  Type *Int1Ty    = Type::getInt1Ty(C);
  Type *Int32Ty    = Type::getInt32Ty(C);
  Type *Int64Ty    = Type::getInt64Ty(C);
  Type *Int32PtrTy = Type::getInt32PtrTy(C);
  Type *VoidPtrTy  = PointerType::getInt8PtrTy(C);

  //====================================================================================================
  BasicBlock * unwindPathEntry = BasicBlock::Create(C, "unwind.path.entry", &F);
  B.SetInsertPoint(unwindPathEntry);
  //====================================================================================================
  // Annotate unwind fucntion
  auto annotateFcn = Intrinsic::getDeclaration(M, Intrinsic::var_annotation);
  auto three = B.getInt32(3); // Indicate that this is a unwind handler
  auto stringptr = B.CreateGlobalStringPtr("test", "unwindhandler");
  CallInst* res = B.CreateCall(annotateFcn, {BlockAddress::get( unwindPathEntry ), stringptr, stringptr, three, stringptr});
  // Somehow need to set this to true to avoid cloberring with the alloca for fork result (analysis restul from MemoryDependency analysis)
  res->setTailCall(true);
  //====================================================================================================
  // Variable needed to pass information between frame
  // TODO: Should be a part of a thread-structure and can be used to pass information between child and parent
  // The amount of stack unwinded: Can be pass through register
  GlobalVariable* gUnwindStackCnt = GetGlobalVariable("unwindStackCnt", Int32Ty, *M, true);
  // The thread id
  GlobalVariable* gThreadId = GetGlobalVariable("threadId", Int32Ty, *M, true);
  // Number of par-for-par encountered
#ifdef PRL_LATER
  GlobalVariable* gParForParEncountered = GetGlobalVariable("parForParEncountered", Int32Ty, *M, true);
#endif
  // Store the original return address (this can be pass through register)
  GlobalVariable* gPrevRa = GetGlobalVariable("prevRa", Int64Ty, *M, true);
  // Store the original return address (this can be pass through register)
  GlobalVariable* gPrevSp = GetGlobalVariable("prevRa", Int64Ty, *M, true);
  // Get the work ctx array : Should be global (persist)
  GlobalVariable* gWorkContext = GetGlobalVariable("workctx_arr",
                                                   workcontext_ty->getPointerTo()->getPointerTo(), *M);

  // Get the context of the program before the unwind: Can be pass through register
  GlobalVariable* gUnwindContext = GetGlobalVariable("unwindCtx", workcontext_ty, *M, true);
  // Save the context in a temporary variable: Can be pass through register
  GlobalVariable* gTmpContext = GetGlobalVariable("tmpCtx", workcontext_ty, *M, true);
  // Get the pointer to the unwind path entry
  GlobalVariable* gSeedSp = GetGlobalVariable("seed_ptr", VoidPtrTy->getPointerTo(), *M, true);
  // Get the pointer to the pointer (persist through out unwinding). It is like SP to a stack.
  GlobalVariable* gBot = GetGlobalVariable("bot", Int32Ty, *M, true);
  // Get the global variable for the pointer
  GlobalVariable* gUnwindStack = GetGlobalVariable("unwindStack", VoidPtrTy, *M, true);
  //
  //====================================================================================================
  // Function Needed
  //Function* getSP = Intrinsic::getDeclaration(M, Intrinsic::read_sp);
  //Function* setSP = Intrinsic::getDeclaration(M, Intrinsic::write_sp);
  //Function* getFrameSize = Intrinsic::getDeclaration(M, Intrinsic::get_frame_size);

  // Constant
  Value* ONE = B.getInt32(1);
  Value* ZERO = B.getInt32(0);
  Value* ZERO64 = B.getInt64(0);
  Value* ONEBYTE = ConstantInt::get(IntegerType::getInt64Ty(C), 8, false);
  Value* NULL8 = ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());

  //====================================================================================================
  // Save the context at a temporary variable
  Value* gPTmpContext = B.CreateConstInBoundsGEP2_64(workcontext_ty, gTmpContext, 0, 0 ); //void**
  auto saveContext = Intrinsic::getDeclaration(M, Intrinsic::uli_save_callee);
  auto res2 = B.CreateCall(saveContext, {B.CreateBitCast(gPTmpContext, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});
  res2->setTailCall(true);

  // Get the SP and BP to get my return address
  Value * gThreadIdVal = B.CreateAlignedLoad(Int32Ty, gThreadId, Align(4));
  Value * gUnwindStackCntVal = B.CreateLoad(Int32Ty, gUnwindStackCnt);

  // The child original return address
  Value * gPrevRaVal = B.CreateLoad(Int64Ty, gPrevRa);

  auto childAddrOfRA = Intrinsic::getDeclaration(M, Intrinsic::uli_child_addressofreturnaddress);
  Value* pChildRA = B.CreateCall(childAddrOfRA);
  pChildRA = B.CreateBitCast(pChildRA, IntegerType::getInt8Ty(C)->getPointerTo()->getPointerTo());

  // Get my return address's address
  auto addrOfRA = Intrinsic::getDeclaration(M, Intrinsic::addressofreturnaddress, {VoidPtrTy});
  Value* myRA = B.CreateCall(addrOfRA);
  myRA = B.CreateBitCast(myRA, IntegerType::getInt64Ty(C)->getPointerTo());

  //====================================================================================================
  // Create basic block that unwind the path
  BasicBlock* unwindPathNewStackBB = BasicBlock::Create(C, "unwind.path.new.stack", &F);
  BasicBlock* firstTimeUnwindBB = BasicBlock::Create(C, "unwind.path.first.time.unwind", &F);
  BasicBlock* jumpTableBB = BasicBlock::Create(C, "unwind.path.jump.table", &F);
  BasicBlock* unwindEpilogueBB = BasicBlock::Create(C, "unwind.path.epilogue", &F);
  // Basic Block needed to keep unwinding or stop unwinding
  BasicBlock* resumeInterruptedBB = BasicBlock::Create(C, "unwind.path.resume.interrupted", &F);
  BasicBlock* returnToUnwindBB = BasicBlock::Create(C, "unwind.path.return.to.unwind", &F);
  BasicBlock* stackAlreadyUnwindBB = BasicBlock::Create(C, "unwind.path.already.unwind", &F);

  // FIXME: first unwindPathNewStackBB should be resumeInterruptedBB
  if(EnableUnwindOnce) {
    BasicBlock* stackAlreadyUnwindCheckBB = BasicBlock::Create(C, "unwind.path.already.unwind.check", &F);

    Value* haveBeenUnwind = nullptr;
#ifdef PRL_LATER
    if(bHaveFork && !(F.getFnAttribute("par-for-par").getValueAsString()=="true")) {
#else
    if(bHaveFork) {
#endif
      Value* bHaveUnwind = B.CreateLoad(Int1Ty, bHaveUnwindAlloc, 1);
      haveBeenUnwind = B.CreateICmpEQ(bHaveUnwind, B.getInt1(1));
    } else {
      haveBeenUnwind = B.CreateICmpEQ(B.getInt1(0), B.getInt1(1));
    }
    //xchg unwind_stack, rsp
#ifndef STICK_STACKXCGH_FUNC
    Value* unwindStack = B.CreateLoad(VoidPtrTy, gUnwindStack);
    Value* mySP = getSP(B, F);
    B.CreateStore(mySP, gPrevSp);
    //using AsmTypeCallee = void (void*);
    FunctionType *FAsmTypeCallee = FunctionType::get(Type::getVoidTy(C), {PointerType::getInt8PtrTy(C)}, false);
    InlineAsm* Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rsp\n", "r,~{rsp},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    B.CreateCall(Asm, {unwindStack});
#endif

    // If first time unwind, resume without changing return address
    B.CreateCondBr(haveBeenUnwind, stackAlreadyUnwindCheckBB, unwindPathNewStackBB);
    B.SetInsertPoint(stackAlreadyUnwindCheckBB);
    Value* isEqZero = B.CreateICmpEQ(gUnwindStackCntVal, ZERO);
    B.CreateCondBr(isEqZero, resumeInterruptedBB, stackAlreadyUnwindBB);

  } else {
    Value* haveBeenUnwind = B.CreateICmpEQ(B.getInt1(0), B.getInt1(1));
    B.CreateCondBr(haveBeenUnwind, stackAlreadyUnwindBB, unwindPathNewStackBB);
  }


  B.SetInsertPoint(unwindPathNewStackBB);

  // if (unwindStackCnt == 0)
  Value* isEqZero = B.CreateICmpEQ(gUnwindStackCntVal, ZERO);
  B.CreateCondBr(isEqZero, firstTimeUnwindBB, jumpTableBB);
  {
    // Basic block for first time unwind
    B.SetInsertPoint(firstTimeUnwindBB);
#ifdef PRL_LATER
    B.CreateStore(B.getInt32(0), gParForParEncountered);
#endif

    // If the function has poll-at loop attribute
    if(F.getFnAttribute("poll-at-loop").getValueAsString()=="true") {
      if(EnableUnwindOnce && !DisableUnwindPoll ) {
#ifndef PRL_LATER
        B.CreateStore(B.getInt1(1), bHaveUnwindAlloc);
#endif
      }
    }

    B.CreateBr(unwindEpilogueBB);
  }
  {
    B.SetInsertPoint(jumpTableBB);

    // Get workctx[threadId]
    // gWorkContext void** * * *
    Value * gWorkContextVal = B.CreateLoad(workcontext_ty->getPointerTo()->getPointerTo(), gWorkContext); //void*[WORKCTX_SIZE] * *
    Value * gWorkContextValPerThread = B.CreateInBoundsGEP(workcontext_ty->getPointerTo(), gWorkContextVal, gThreadIdVal); // workctx[threadId] void*[WORKCTX_SIZE] **
    Value * gWorkContextValPerThreadVal = B.CreateLoad(workcontext_ty->getPointerTo(), gWorkContextValPerThread); //void*[WORKCTX_SIZE] *

    BasicBlock * nextBlock = jumpTableBB;

    // Check if there is a parallel tasks (create a table)
    for (auto detachInst: bbOrder) {
      B.SetInsertPoint(nextBlock);

      BasicBlock* pBB = detachInst->getParent();
      BasicBlock* detachBB = detachInst->getDetached();
      BasicBlock* contBB = detachInst->getContinue();
      BasicBlock* gotStolenHandler = dyn_cast<BasicBlock>(VMapGotStolenPath[detachBB]);
      Value* ra = gPrevRaVal;

      Value* rai = B.CreateCast(Instruction::PtrToInt, ra, IntegerType::getInt64Ty(C));
      Value* detachBBi = B.CreateCast(Instruction::PtrToInt, BlockAddress::get(detachBB), IntegerType::getInt64Ty(C));
      Value* contBBi = B.CreateCast(Instruction::PtrToInt, BlockAddress::get(contBB), IntegerType::getInt64Ty(C));

      BasicBlock* workExistsBB = BasicBlock::Create(C, "unwind.path.work.exists", &F);
      BasicBlock* workExistsBB2 = BasicBlock::Create(C, "unwind.path.work.exists.two", &F);
      BasicBlock* noworkBB = BasicBlock::Create(C, "unwind.path.nowork", &F);

      // Check if the return address has work to do
      Value* fastPathCont = B.CreateCast(Instruction::PtrToInt, BlockAddress::get(detachBB, 0), IntegerType::getInt64Ty(C));
      auto isEqOne1 = (B.CreateICmpEQ(rai, fastPathCont));

#ifdef PRL_LATER
      if(F.getFnAttribute("par-for-par").getValueAsString()=="true") {
	Value* bHaveUnwind = B.CreateLoad(Int1Ty, bHaveUnwindAlloc, 1);
	// If already encounted a par-for-par
	Value* bHaveEncountered = B.CreateLoad(Int32Ty, gParForParEncountered, 1);
	Value* comb = B.CreateOr(B.CreateICmpEQ(bHaveEncountered, B.getInt32(1)), bHaveUnwind);
	isEqOne1 = B.CreateAnd(isEqOne1, comb);
      }
#endif

      B.CreateCondBr(isEqOne1, workExistsBB, noworkBB);

      B.SetInsertPoint(workExistsBB);
      B.CreateBr(workExistsBB2);

      B.SetInsertPoint(workExistsBB2);

      // When work is created during uwinding, set bHaveUnwind to 1.
      // FIXME: Not optimal solution since parent without any child can be unwind more than once.
      if(EnableUnwindOnce && !DisableUnwindPoll ) {
        B.CreateStore(B.getInt1(1), bHaveUnwindAlloc);
      }

      // Store gotstolen handler to child return address
      auto actualDetachBB = getBBContainReattached(detachBB);

      B.CreateStore(BlockAddress::get(actualDetachBB, GOTSTOLEN_INDEX), pChildRA);

      // Update context for particular stack
      // *(&bot)
      Value* botVal = B.CreateLoad(Int32Ty, gBot);

      // 1. Move the callee saved register
      // 2. Set the rip
      // 3. The join counter
      // 4. threadId
      // 5. Location of work
      // Use below to convert void[64]* to void**
      //B.CreateConstInBoundsGEP2_64(gTmpContext, 0, 0 ); //void**

      Value* gWorkContextValPerThreadPerBot = B.CreateInBoundsGEP(workcontext_ty, gWorkContextValPerThreadVal, botVal);
      Value* gWorkContextPtr = B.CreateConstInBoundsGEP2_64(workcontext_ty, gWorkContextValPerThreadPerBot, 0, 0 ); //void**

      // Savee the callee register
#ifdef OPTIMIZE_UNWIND
      Value* tmpRBP = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gPTmpContext, I_RBP);
      Value* tmpRSP = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gPTmpContext, I_RSP);
      Value* tmpR11 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gPTmpContext, I_R11);
      Value* tmpRBX = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gPTmpContext, I_RBX);
      Value* tmpR12 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gPTmpContext, I_R12);
      Value* tmpR13 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gPTmpContext, I_R13);
      Value* tmpR14 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gPTmpContext, I_R14);
      Value* tmpR15 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gPTmpContext, I_R15);

      Value* savedRBP = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gWorkContextPtr, I_RBP);
      Value* savedRSP = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gWorkContextPtr, I_RSP);
      Value* savedR11 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gWorkContextPtr, I_R11);
      Value* savedRBX = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gWorkContextPtr, I_RBX);
      Value* savedR12 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gWorkContextPtr, I_R12);
      Value* savedR13 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gWorkContextPtr, I_R13);
      Value* savedR14 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gWorkContextPtr, I_R14);
      Value* savedR15 = B.CreateConstGEP1_32(gPTmpContext->getType()->getScalarType()->getPointerElementType(), gWorkContextPtr, I_R15);

      B.CreateStore(B.CreateLoad(VoidPtrTy, tmpRBP), savedRBP);
      B.CreateStore(B.CreateLoad(VoidPtrTy, tmpRSP), savedRSP);
      B.CreateStore(B.CreateLoad(VoidPtrTy, tmpR11), savedR11);
      B.CreateStore(B.CreateLoad(VoidPtrTy, tmpRBX), savedRBX);
      B.CreateStore(B.CreateLoad(VoidPtrTy, tmpR12), savedR12);
      B.CreateStore(B.CreateLoad(VoidPtrTy, tmpR13), savedR13);
      B.CreateStore(B.CreateLoad(VoidPtrTy, tmpR14), savedR14);
      B.CreateStore(B.CreateLoad(VoidPtrTy, tmpR15), savedR15);

#ifdef OPTIMIZE_UNWIND_FUNC
      // Call a function to update parallel context (ip, join counter, owner of work, location, locRef
#ifdef STICK_STACKXCGH_FUNC
    Value* unwindStack = B.CreateLoad(VoidPtrTy, gUnwindStack);
    Value* mySP = getSP(B, F);
    B.CreateStore(mySP, gPrevSp);
#ifdef OPTIMIZE_FP
    auto unwindStackInt = B.CreateCast(Instruction::PtrToInt, unwindStack, IntegerType::getInt64Ty(C));
    setSP(B, F, unwindStackInt);
#else
    //using AsmTypeCallee = void (void*);
    FunctionType *FAsmTypeCallee = FunctionType::get(Type::getVoidTy(C), {PointerType::getInt8PtrTy(C)}, false);
    InlineAsm* Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rsp\n", "r,~{rsp},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    B.CreateCall(Asm, {unwindStack});
#endif
#endif
    Value* locAllocAsPointer = B.CreateBitCast(locAlloc, IntegerType::getInt8Ty(C)->getPointerTo());
    FunctionCallee initialize_parallel_ctx = Get_initialize_parallel_ctx(*M);
    B.CreateCall(initialize_parallel_ctx, {gWorkContextPtr, BlockAddress::get(actualDetachBB, STEALENTRY_INDEX), locAllocAsPointer});
#ifdef STICK_STACKXCGH_FUNC
    Value* prevSP = B.CreateLoad(Int64Ty, gPrevSp);
#ifdef OPTIMIZE_FP
    setSP(B, F, prevSP);
#else
    using AsmTypeCallee2 = void (long);
    FunctionType *FAsmTypeCallee2 = FunctionType::get(Type::getVoidTy(C), {Type::getInt64Ty(C)}, false);
    InlineAsm* Asm2 = InlineAsm::get(FAsmTypeCallee2, "movq $0, %rsp\n", "r,~{rsp},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    B.CreateCall(Asm2, {prevSP});
#endif
#endif

#else
    // Store the address of the slow path entry into the temporary context
    Value* savedPc = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gWorkContextPtr, I_RIP); //void** (no loading involved)

    // workctx[I_RIP] = slow_path_entry;
    B.CreateStore(BlockAddress::get(actualDetachBB, STEALENTRY_INDEX), savedPc);

    // Set join counter to 2
    // workctx[joinctr] = (void*) 2;
    Value* twoAsPointer = B.CreateCast(Instruction::IntToPtr, B.getInt32(2), IntegerType::getInt8Ty(C)->getPointerTo());
    Value* joinCtr = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gWorkContextPtr, I_JOINCNT); //void** (no loading involved)
    B.CreateStore(twoAsPointer, joinCtr);

    // Set the owner of the work
    // workctx[owner] = (void*) threadId;
    Value* threadIdAsPointer = B.CreateCast(Instruction::IntToPtr, gThreadIdVal, IntegerType::getInt8Ty(C)->getPointerTo());
    Value* ownerRef = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gWorkContextPtr, I_OWNER); //void** (no loading involved)
    B.CreateStore(threadIdAsPointer, ownerRef);

    // Set the location of the work
    // workctx[loc] = (void*) bot;
    Value* botAsPointer = B.CreateCast(Instruction::IntToPtr, botVal, IntegerType::getInt8Ty(C)->getPointerTo());
    Value* locRef = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gWorkContextPtr, I_LOC); //void** (no loading involved)
    B.CreateStore(botAsPointer, locRef);

    // Set the address of the location
    // workctx[addrloc] = (void*) (&loc);
    Value* locAllocAsPointer = B.CreateBitCast(locAlloc, IntegerType::getInt8Ty(C)->getPointerTo());
    Value* locAllocRef = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gWorkContextPtr, I_ADDRLOC); //void** (no loading involved)
    B.CreateStore(locAllocAsPointer, locAllocRef);

#endif

    // Store in stack memory
    B.CreateStore(botVal, locAlloc);
    B.CreateStore(gThreadIdVal, ownerAlloc);


#else

    // Store the address of the slow path entry into the temporary context
    Value* savedPc = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gPTmpContext, I_RIP); //void** (no loading involved)

    B.CreateStore(BlockAddress::get(actualDetachBB, STEALENTRY_INDEX), savedPc);

    // Set join counter to 2
    // workctx[joinctr] = (void*) 2;
    Value* twoAsPointer = B.CreateCast(Instruction::IntToPtr, B.getInt32(2), IntegerType::getInt8Ty(C)->getPointerTo());

    Value* joinCtr = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gPTmpContext, I_JOINCNT); //void** (no loading involved)
    B.CreateStore(twoAsPointer, joinCtr);

    // Set the owner of the work
    // workctx[owner] = (void*) threadId;
    Value* threadIdAsPointer = B.CreateCast(Instruction::IntToPtr, gThreadIdVal, IntegerType::getInt8Ty(C)->getPointerTo());

    Value* ownerRef = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gPTmpContext, I_OWNER); //void** (no loading involved)
    B.CreateStore(threadIdAsPointer, ownerRef);

    // Set the location of the work
    // workctx[loc] = (void*) bot;
    Value* botAsPointer = B.CreateCast(Instruction::IntToPtr, botVal, IntegerType::getInt8Ty(C)->getPointerTo());
    Value* locRef = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gPTmpContext, I_LOC); //void** (no loading involved)

    B.CreateStore(botAsPointer, locRef);
    // Store in memory
    B.CreateStore(botVal, locAlloc);

    B.CreateStore(gThreadIdVal, ownerAlloc);

    // Set the address of the location
    // workctx[addrloc] = (void*) (&loc);
    Value* locAllocAsPointer = B.CreateBitCast(locAlloc, IntegerType::getInt8Ty(C)->getPointerTo());

    Value* locAllocRef = B.CreateConstGEP1_32(VoidPtrTy->getPointerTo(), gPTmpContext, I_ADDRLOC); //void** (no loading involved)

    B.CreateStore(locAllocAsPointer, locAllocRef);

    // TODO: Should remove this, maybe expensive
    // Store work
    // Save the tmpCtx into the workCtx[threadId][bot]
    //Value * gWorkContextValPerThreadPerBot = B.CreateInBoundsGEP(gWorkContextValPerThreadVal, botVal);
    Value* gTmpContextVal = B.CreateLoad(workcontext_ty, gTmpContext);
    B.CreateStore(gTmpContextVal ,gWorkContextValPerThreadPerBot);
#endif

#if 0
    // Store pointer to work
    gWorkContextValPerThreadPerBot->dump();
    gWorkContextValPerThreadPerBot->getType()->dump();

    locAlloc->dump();
    locAlloc->getType()->dump();
    //B.CreateStore(gWorkContextValPerThreadPerBot ,locAlloc);
    B.CreateStore(gTmpContextVal, locAlloc);
#endif

    // Update workctx pointer
    B.CreateStore(B.CreateAdd(botVal,ONE), gBot);

    B.CreateBr(unwindEpilogueBB);
    nextBlock = noworkBB;
    }

    B.SetInsertPoint(nextBlock);

    //if(EnableUnwindOnce2) {
    //  B.CreateStore(gPrevRaToVoid, pChildRA);
    //} else {
    // Store the original return address to child return address
#ifdef PRL_LATER
    if(F.getFnAttribute("par-for-par").getValueAsString()=="true") {
      if(EnableUnwindOnce && !DisableUnwindPoll ) {
        B.CreateStore(B.getInt1(1), bHaveUnwindAlloc);
	B.CreateStore(B.getInt32(1), gParForParEncountered);
      }
    }
#endif

    Value * gPrevRaToVoid = B.CreateCast(Instruction::IntToPtr, gPrevRaVal, IntegerType::getInt8Ty(C)->getPointerTo());
    B.CreateStore(gPrevRaToVoid, pChildRA);
    //}

    if(F.getFnAttribute("poll-at-loop").getValueAsString()=="true") {
      if(EnableUnwindOnce && !DisableUnwindPoll ) {
#ifndef PRL_LATER
        B.CreateStore(B.getInt1(1), bHaveUnwindAlloc);
#endif
      }
    }

    B.CreateBr(unwindEpilogueBB);

    // If stack have been unwind already
    B.SetInsertPoint(stackAlreadyUnwindBB);
    Value * gPrevRaToVoid_2 = B.CreateCast(Instruction::IntToPtr, gPrevRaVal, IntegerType::getInt8Ty(C)->getPointerTo());
    B.CreateStore(gPrevRaToVoid_2, pChildRA);
    B.CreateBr(resumeInterruptedBB);
  }
  // Prepare to return or keep unwinding
  B.SetInsertPoint(unwindEpilogueBB);

  // Increment the counter
  B.CreateStore(B.CreateAdd(gUnwindStackCntVal, ONE), gUnwindStackCnt);
  //====================================================================================================

  Value* unwindEntryVal = nullptr;
  Value* unwindAddrRes = nullptr;
  // Get the unwind path entry based on return address
#ifdef STICK_STACKXCGH_FUNC
  Value* unwindStack = B.CreateLoad(VoidPtrTy, gUnwindStack);
  Value* mySP = getSP(B, F);
  B.CreateStore(mySP, gPrevSp);
#ifdef OPTIMIZE_FP
  auto unwindStackInt = B.CreateCast(Instruction::PtrToInt, unwindStack, IntegerType::getInt64Ty(C));
  setSP(B, F, unwindStackInt);
#else
  using AsmTypeCallee = void (void*);
  FunctionType *FAsmTypeCallee = FunctionType::get(Type::getVoidTy(C), {PointerType::getInt8PtrTy(C)}, false);
  InlineAsm* Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rsp\n", "r,~{rsp},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
  B.CreateCall(Asm, {unwindStack});
#endif
#endif
  FunctionCallee queryUnwindAddr = UNWINDRTS_FUNC(unwind_queryunwindaddress, *M);
  auto loadRA = B.CreateLoad(Int64Ty, myRA); // myRA: int64*, loadRA: int64
  unwindAddrRes = B.CreateCall(queryUnwindAddr, {loadRA});
  unwindEntryVal = B.CreateZExt(unwindAddrRes, IntegerType::getInt64Ty(C));
#ifdef STICK_STACKXCGH_FUNC
  Value* prevSP = B.CreateLoad(Int64Ty, gPrevSp);
#ifdef OPTIMIZE_FP
  setSP(B, F, prevSP);
#else
  using AsmTypeCallee2 = void (long);
  FunctionType *FAsmTypeCallee2 = FunctionType::get(Type::getVoidTy(C), {Type::getInt64Ty(C)}, false);
  InlineAsm* Asm2 = InlineAsm::get(FAsmTypeCallee2, "movq $0, %rsp\n", "r,~{rsp},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
  B.CreateCall(Asm2, {prevSP});
#endif
#endif

  //====================================================================================================
  // if (*p_parent_unwind == 0)
  Value* isEqZero64 = B.CreateICmpEQ(unwindEntryVal, ZERO64);
  B.CreateCondBr(isEqZero64, resumeInterruptedBB, returnToUnwindBB);

  {
    B.SetInsertPoint(resumeInterruptedBB);

    //B.CreateStore(ZERO, gUnwindStackCnt);
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(workcontext_ty, gUnwindContext, 0, 0 );

    auto restoreContext = Intrinsic::getDeclaration(M, Intrinsic::uli_restore_context);
    //restoreContext->addFnAttr(Attribute::Forkable);
    CallInst* result = B.CreateCall(restoreContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(C)->getPointerTo())});
    //result->setTailCall(true);

    B.CreateUnreachable();
  }
  //====================================================================================================
  {
    B.SetInsertPoint(returnToUnwindBB);

    // Switch stack
#ifndef STICK_STACKXCGH_FUNC
    Value* prevSP = B.CreateLoad(Int64Ty, gPrevSp);
    using AsmTypeCallee = void (long);
    FunctionType *FAsmTypeCallee = FunctionType::get(Type::getVoidTy(C), {Type::getInt64Ty(C)}, false);
    InlineAsm* Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rsp\n", "r,~{rsp},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    B.CreateCall(Asm, {prevSP});
#endif

    // Change the gPrevRa to my return address
    B.CreateStore(B.CreateLoad(Int64Ty, myRA), gPrevRa);
    // Change my return address to unwnd entry
    B.CreateStore(unwindEntryVal, myRA);

    // Restore back the calleee
    auto restoreCallee = Intrinsic::getDeclaration(M, Intrinsic::uli_restore_callee);
    B.CreateCall(restoreCallee, {B.CreateBitCast(gPTmpContext, IntegerType::getInt8Ty(C)->getPointerTo())});

    // Restore rsp to get proper stack (if there is only dynamic alloca)
#ifdef OPTIMIZE_FP
    if(bHaveFork || bHaveCallFcn6Args) {
#else
    if(true) {
#endif
      Function *SetupRSPfromRBP = Intrinsic::getDeclaration(M, Intrinsic::setup_rsp_from_rbp);
      B.CreateCall(SetupRSPfromRBP);
    }

    // return 0; or anything empty
    if(F.getReturnType()->isVoidTy()) {
      B.CreateRetVoid();
    } else if (F.getReturnType()->isIntegerTy()) {
      B.CreateRet(ConstantInt::get(F.getReturnType(), 0, false));
    } else if (F.getReturnType()->isPointerTy()) {
      B.CreateRet(ConstantPointerNull::get(dyn_cast<PointerType>(F.getReturnType())));
    } else if (F.getReturnType()->isFloatingPointTy()) {
      B.CreateRet(ConstantFP::get(F.getReturnType(), "0"));
    } else if (F.getReturnType()->isStructTy()) {
      B.CreateRet(PoisonValue::get(F.getReturnType()));
    } else if (F.getReturnType()->isArrayTy()) {
      B.CreateRet(PoisonValue::get(F.getReturnType()));
    } else if (F.getReturnType()->isVectorTy()) {
      B.CreateRet(PoisonValue::get(F.getReturnType()));
    } else {
      errs() << "Have not supported " << *F.getReturnType() << " yet\n";
      assert(0 && "Return type not supported yet");
    }

  }
  //====================================================================================================
  return unwindPathEntry;
}

// Get the live variables after the detached block (live out)
// Create a store for it.
// Create a load for it in the restore path
// Add potential jump to got stolen handler
void LazyDTransPass::createGotStolenHandler(SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,
                            Value* locAlloc, Value* ownerAlloc,
                            DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>& LVout,
                            DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                            ValueToValueMapTy& VMapSlowPath,
                            ValueToValueMapTy& VMapGotStolenPath) {
  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  // Iterate over the whole detach inst.
  for (auto detachInst: bbOrder) {
    BasicBlock* pBB = detachInst->getParent();
    assert(pBB);
    BasicBlock* detachBB = detachInst->getDetached();
    BasicBlock* continueBB = detachInst->getContinue();

    // For each detach instruction, create a gotstolen handler
    auto gotStolenHandler = createGotStolenHandlerBB(*detachInst, continueBB, locAlloc, ownerAlloc);
    // Map the det.achd with its gotstolen handler
    VMapGotStolenPath[detachBB] = gotStolenHandler;

#if 0
    auto liveOutVars = LVout[detachBB];
    auto liveInVars = LVin[detachBB][detachBB->getUniquePredecessor()];

    errs() << "For basic block " << detachBB->getName() << " live variables out: \n";
    // Since in cilk, the return variable is immediately stored in memory, there should be no live variables
    // Look for live variables inside
    for (auto liveOutVar : liveOutVars) {
      if(liveInVars.find(liveOutVar) == liveInVars.end())
        liveOutVar->dump();
    }

    errs() << "For basic block " << detachBB->getName() << " live variables in: \n";
    // Since in cilk, the return variable is immediately stored in memory, there should be no live variables
    // Look for live variables inside
    for (auto liveInVar : liveInVars) {
      for (auto &use : liveInVar->uses()) {
        auto * user = dyn_cast<Instruction>(use.getUser());
        if(user->getParent() == detachBB) {
          liveInVar->dump();
        }
      }
    }
#endif

  }
}

// Create a gotstolen handler for the Detach inst
// It contains instruction after the call (storing result etc.), runtime to jump to the scheduler etc.
BasicBlock * LazyDTransPass::createGotStolenHandlerBB(DetachInst& Detach, BasicBlock* contBB, Value* locAlloc, Value* ownerAlloc) {
  BasicBlock* curBB = Detach.getParent();
  Function* F = curBB->getParent();
  Module* M = F->getParent();
  LLVMContext& C = F->getContext();

  Instruction * spawnCI = nullptr;
  FunctionCallee suspend2scheduler = Get_suspend2scheduler(*M);
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::uli_potential_jump);

  // Get the detach basic block
  BasicBlock * detachBB = Detach.getDetached();
  detachBB = getBBContainReattached(detachBB);

  BasicBlock * stolenHandlerPathEntry = BasicBlock::Create(C, "gotstolenhandler", F);

  IRBuilder<> builder(C);
  SmallVector<Instruction*, 4> workList;
  Instruction * startOfclone = nullptr;

  Type* Int32Ty = IntegerType::getInt32Ty(C);

  // Add potential jump from detachBB to got stolen handler
  for (auto &II: *detachBB) {
    workList.push_back(&II);
  }
  // Find the fork inst
  while (!workList.empty()) {
    Instruction &II = *workList.pop_back_val();

    // Found the fork instruction
    if(isa<MultiRetCallInst>(&II)) {
      auto mrc = dyn_cast<MultiRetCallInst>(&II);
      // Perform a branch to gotstolen handler bb
      auto bb2 = mrc->getIndirectDest(1);
      builder.SetInsertPoint(bb2);
      builder.CreateRetPad(mrc);
      builder.CreateBr(stolenHandlerPathEntry);

      auto defaultBB = mrc->getDefaultDest();
      // Attempt to clone after calll until reattach inst
      startOfclone = defaultBB->getFirstNonPHIOrDbgOrLifetime()->getNextNode();

      spawnCI = mrc;
    }
  }

  assert(startOfclone && "Can not find instruction to clone");

  builder.SetInsertPoint(stolenHandlerPathEntry);

  // Call the parallel runtime to suspend to scheduler
  Value * locVal = builder.CreateLoad(Int32Ty, locAlloc, 1, "locVal");
  Value * ownerVal = builder.CreateLoad(Int32Ty, ownerAlloc, 1, "ownerVal");
  Instruction * insertInst = builder.CreateCall(suspend2scheduler, {locVal, ownerVal, builder.getInt32(0)});
  dyn_cast<CallInst>(insertInst)->setTailCall(false);

  // Terminate the gotstolen handler
  builder.CreateUnreachable();


  // Clone instruction after call
  SmallVector<Instruction *, 4> inst2delete;
  SmallVector<Instruction *, 4> insts2clone;

  // Stop after the reattach is found
  Instruction* ii = startOfclone;
  while(!isa<ReattachInst>(ii)) {
    insts2clone.push_back(ii);
    ii = ii->getNextNode();
  }

  ValueToValueMapTy VMapGotStolenI;

  // Look for the clone store instruction and set it to volatile
  for(auto ii: insts2clone) {
    Instruction * iiClone = ii->clone();
    iiClone->insertBefore(insertInst);
    VMapGotStolenI[ii] = iiClone;
    //insertInst = iiClone;
    if(isa<StoreInst>(iiClone)) {
      dyn_cast<StoreInst>(iiClone)->setVolatile(true);
    }
  }

  // Get all uses of the clone instruction and replace it
  SmallVector< Use*, 4 >  useNeed2Update;
  for(auto ii: insts2clone) {
    useNeed2Update.clear();

    if(isa<StoreInst>(ii))
      continue;
    Instruction * gotStolenI = dyn_cast<Instruction>(VMapGotStolenI[ii]);

    for (auto &use : ii->uses()) {
      auto * user = dyn_cast<Instruction>(use.getUser());
      if(user->getParent() == stolenHandlerPathEntry) {
        useNeed2Update.push_back(&use);
      }
    }
    for( auto U : useNeed2Update ){
      U->set(gotStolenI);
    }
  }
  builder.SetInsertPoint(stolenHandlerPathEntry->getFirstNonPHIOrDbgOrLifetime());

  // Create a variable annotation indicating that this either a gotstolen handler: 0
  Function*  annotateFcn = Intrinsic::getDeclaration(M, Intrinsic::var_annotation);
  auto parentSpawn = spawnCI->getParent();
  auto parentBA = BlockAddress::get( parentSpawn );
  auto zero = builder.getInt32(0);
  auto stringptr = builder.CreateGlobalStringPtr("test", "gotstolen");
  CallInst* res = builder.CreateCall(annotateFcn, {parentBA, stringptr, stringptr, zero, stringptr});
  // Somehow need to set this to true to avoid cloberring with the alloca for fork result (analysis restul from MemoryDependency analysis)
  res->setTailCall(true);
  // Return the stolen handler
  return stolenHandlerPathEntry;
}

void LazyDTransPass::instrumentSlowPath(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,
                        Value* locAlloc, Value* ownerAlloc, Value* bHaveUnwindAlloc, Value* fromSlowPathAlloc, SmallVector<SyncInst*, 8>& syncInsts, ValueToValueMapTy&  VMapSlowPath,
                        DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB,
                        SSAUpdater& SSAUpdateWorkContext){

  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  Type *VoidPtrTy  = PointerType::getInt8PtrTy(C);
  Type* Int32Ty = IntegerType::getInt32Ty(C);

  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  // Loop through the detach basic block that corresponds to the slow path
  for (auto di : bbOrder) {
    auto pBB = di->getParent();
    assert(pBB);

    // Get the slow path version
    auto diSlowPath = dyn_cast<DetachInst>(VMapSlowPath[di]);
    auto pBBSlowPath = diSlowPath->getParent();
    assert(diSlowPath && "Detach basic block should not have been modified, invariant not met");

    // Ignore detach that do not have any reaching detaches (since these detaches do not exist in the slow path)
    if(RDIBB[di].empty()) continue;

    // Convert detach into
    /*
    det.cont.tf.slowPath:                             ; preds = %det.achd
      %10 = call i64 @llvm.read_register.i64(metadata !3)
      %11 = inttoptr i64 %10 to i8*
      %locVal99 = load volatile i32, i32* %loc, align 4
      %owner.0.owner.0.owner.0.owner.0.ownerVal100 = load volatile i32, i32* %owner, align 4
      %12 = call i8** @get_workcontext_locowner(i32 %locVal99, i32 %owner.0.owner.0.owner.0.owner.0.ownerVal100, i8* %11) #19
      %13 = bitcast i8** %12 to i8*
      call void @llvm.uli.save.context.nosp(i8* %13, i8* null)
      multiretcall void @llvm.donothing()
      to label %det.achd8.slowPath [label %det.cont9.tf.slowPath ]

    */
    auto detachedSlowPath = diSlowPath->getDetached();
    auto continueSlowPath = diSlowPath->getContinue();

    B.SetInsertPoint(diSlowPath);

    auto detachBB = di->getDetached();
    auto actualDetachBB = getBBContainReattached(detachBB);

    auto multiRetCall = dyn_cast<MultiRetCallInst>(actualDetachBB->getTerminator());
    assert(multiRetCall && "Terminator is not multiretcall inst");

    // Get the workctx
    // workctx contains information related to running the parallel task, such as join counter callee register, etc.
    /*
    det.cont.tf.slowPath:                             ; preds = %det.achd
      %10 = call i64 @llvm.read_register.i64(metadata !3)
      %11 = inttoptr i64 %10 to i8*
      %locVal99 = load volatile i32, i32* %loc, align 4
      %owner.0.owner.0.owner.0.owner.0.ownerVal100 = load volatile i32, i32* %owner, align 4
      %12 = call i8** @get_workcontext_locowner(i32 %locVal99, i32 %owner.0.owner.0.owner.0.owner.0.ownerVal100, i8* %11) #19
      .....
   */
    Value* mySP = getSP(B, F);
    mySP = B.CreateCast(Instruction::IntToPtr, mySP, IntegerType::getInt8Ty(C)->getPointerTo());
    FunctionCallee GetWorkCtxFcnCall = Get_get_workcontext_locowner(*M);
    Value* workCtx = B.CreateCall(GetWorkCtxFcnCall, {B.CreateLoad(Int32Ty, locAlloc, 1, "locVal"), B.CreateLoad(Int32Ty, ownerAlloc, 1, "ownerVal"), mySP});
    // Create the multiretcall: Inform that the continuation can be executed in parallel with the det.achd block
    /*
    det.cont.tf.slowPath:                             ; preds = %det.achd
      .....
      %13 = bitcast i8** %12 to i8*
      call void @llvm.uli.save.context.nosp(i8* %13, i8* null)
      multiretcall void @llvm.donothing()  to label %det.achd8.slowPath [label %det.cont9.tf.slowPath ]
    */
    Value* NULL8 = ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
    auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);
    auto saveContextNoSP = Intrinsic::getDeclaration(M, Intrinsic::uli_save_context_nosp);
    auto res = B.CreateCall(saveContextNoSP, {B.CreateBitCast(workCtx, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});
    auto insertPoint = B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), detachedSlowPath, {continueSlowPath}, {});
    diSlowPath->eraseFromParent();

    // Replace reattach with branch (if detach is removed, reattach should also remove, otherwise invariant assume in passes is not met
    /*
      det.achd8.slowPath:                               ; preds = %det.cont.tf.slowPath
       .....
       br label %det.cont9.tf.slowPath
    */
    auto actualDetachedSlowPath = getBBContainReattached(detachedSlowPath);
    ReattachInst* reattachInst = dyn_cast<ReattachInst>(actualDetachedSlowPath->getTerminator());
    BasicBlock* contBB = reattachInst->getDetachContinue();
    BranchInst* brInst = BranchInst::Create(contBB);
    ReplaceInstWithInst(reattachInst, brInst);

    // Call the function wrapper that enables parallelism
    B.SetInsertPoint(detachedSlowPath->getFirstNonPHIOrDbgOrLifetime());

    /*
      det.achd8.slowPath:                               ; preds = %det.cont.tf.slowPath
      %14 = getelementptr i8*, i8** %12, i64 1
      store i8* blockaddress(@cilksort, %det.cont.tf.slowPath) successor  i32 1, i8** %14, align 8
      ...
    */
    Value* savedPc = B.CreateConstGEP1_32(VoidPtrTy, workCtx, 1);
    B.CreateStore(BlockAddress::get(pBBSlowPath, 1), savedPc);

    // Clone the instruction after the forked function
    bool bStartClone = false;
    SmallVector<Instruction *, 4> insts2clone;
    SmallPtrSet<Instruction *, 4> insts2cloneSet;
    CallInst* ci = nullptr;
    for(auto &ii : *detachedSlowPath) {
      if(bStartClone) {
        if(isa<ReattachInst>(&ii) || isa<BranchInst>(&ii)) {
          break;
        }
        insts2clone.push_back(&ii);
        insts2cloneSet.insert(&ii);
      }
      if(!bStartClone && isa<CallInst>(&ii) && !isa<IntrinsicInst>(&ii)) {
        ci = dyn_cast<CallInst>(&ii);
        bStartClone = true;
        if(ci->getFunctionType()->getReturnType()->isVoidTy()) {
          break;
        }
      }
    }
    assert(ci && "No call inst found in slowpath");

    // Find variables used by clone function but defined outside
    // Used as an argument to the wrapper
    SmallPtrSet<Value*, 8> OutsideVars;
    for(auto ii : insts2clone) {
      for (Use &U : ii->operands()) {
        Value *v = U.get();
        if(v && isa<Instruction>(v) ) {
          auto instV = dyn_cast<Instruction>(v);
          if(insts2cloneSet.find(instV) == insts2cloneSet.end() && instV  != ci)
            OutsideVars.insert(v);
        } else if (v && isa<Argument>(v)) {
          OutsideVars.insert(v);
        }
      }
    }

    // Prepare the call and argument
    /*
      det.achd8.slowPath:                               ; preds = %det.cont.tf.slowPath
      .....
      %15 = call i64 @llvm.read_register.i64(metadata !3)
      %16 = inttoptr i64 %15 to i8*
      %locVal101 = load volatile i32, i32* %loc, align 4
      %owner.0.owner.0.owner.0.owner.0.ownerVal102 = load volatile i32, i32* %owner, align 4
      %17 = call i8** @get_workcontext_locowner(i32 %locVal101, i32 %owner.0.owner.0.owner.0.owner.0.ownerVal102, i8* %16) #19
    */
    B.SetInsertPoint(detachedSlowPath->getTerminator());
    mySP = getSP(B, F);
    mySP = B.CreateCast(Instruction::IntToPtr, mySP, IntegerType::getInt8Ty(C)->getPointerTo());
    workCtx = B.CreateCall(GetWorkCtxFcnCall, {B.CreateLoad(Int32Ty, locAlloc, 1, "locVal"), B.CreateLoad(Int32Ty, ownerAlloc, 1, "ownerVal"), mySP});

    // Generate the wrapper function
    Function* wrapperFcn = nullptr;
    wrapperFcn = generateWrapperFuncForSlowPath(ci, OutsideVars, insts2clone, workCtx->getType());

    // Add attribute to the wrapper function
    wrapperFcn->addFnAttr(Attribute::NoUnwindPath);
    wrapperFcn->addFnAttr(Attribute::NoInline);
    wrapperFcn->addFnAttr(Attribute::OptimizeNone); // Can cause a ud2 in assembly?
    wrapperFcn->addFnAttr("no-frame-pointer-elim-non-leaf", "true");
    //wrapperFcn->addFnAttr("no-realign-stack");
    //auto Attrs = wrapperFcn->getAttributes();
    //StringRef ValueStr("true" );
    //Attrs = Attrs.addAttribute(wrapperFcn->getContext(), AttributeList::FunctionIndex,
    //                           "no-frame-pointer-elim", ValueStr);
    //wrapperFcn->setAttributes(Attrs);
    wrapperFcn->addFnAttr("no-frame-pointer-elim");


    // Prepare the argument for the wrapper function
    SmallVector<Value*, 4> args;
    // Original argument
    for(int i = 0; i<ci->arg_size(); i++){
      args.push_back(ci->getArgOperand(i));
    }
    // Additional argument
    args.push_back(workCtx);
    args.push_back(mySP);

    // Represent argument that is used by det.achd, but defined outside
    if(!ci->getFunctionType()->getReturnType()->isVoidTy()) {
      for(auto OutsideVar : OutsideVars) {
        args.push_back(OutsideVar);
      }
    }

    // Create the call and remove instruction that is already inside the call
    /*
      det.achd8.slowPath:                               ; preds = %det.cont.tf.slowPath
      .......
      call fastcc void @__prsc_cilksortWrapper(i64* %add.ptr2, i64* %add.ptr3, i64 %div, i8** %17, i8* %16) #19
    */
    B.CreateCall(wrapperFcn, {args});
    while(!insts2clone.empty()) {
      auto ii = insts2clone.back();
      insts2clone.pop_back();
      ii->eraseFromParent();
    }
    ci->eraseFromParent();
  }

  Value* NULL8 = ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
  // Not modify the sync instruction in the slow path
  // Get the sync instruction that corresponds to the slow path
  for(auto syncInst : syncInsts) {
    auto syncBB = syncInst->getParent();
    auto syncSlowPath = dyn_cast<SyncInst>(VMapSlowPath[syncInst]);
    auto syncBBSlowPath = syncSlowPath->getParent();

    assert(syncSlowPath && "Sync inst should not have been modified, invariant not met");
    assert(syncBBSlowPath && "Sync basic block should not have been modified, invariant not met");

    BasicBlock* syncSaveCtxBB = BasicBlock::Create(C, "sync.savectx", &F);
    BasicBlock* syncRuntimeBB = BasicBlock::Create(C, "sync.resume.to.scheduler", &F);
    BasicBlock* syncSucc = syncSlowPath->getSuccessor(0);

    // Generate something like this
    /*
    det.cont11.slowPath:                              ; preds = %det.achd10, %det.achd10.slowPath, %det.cont9.tf.slowPath
      %mul.neg.slowPath = mul nsw i64 %div, -3
      %sub.slowPath = add i64 %mul.neg.slowPath, %size
      tail call void @cilksort(i64* noundef %add.ptr6, i64* noundef %add.ptr7, i64 noundef %sub.slowPath) #19
      store i8 1, i8* getelementptr inbounds (%struct._request_channel, %struct._request_channel* @req_local, i64 0, i32 2), align 2
      %26 = call i64 @llvm.read_register.i64(metadata !3)
      %27 = inttoptr i64 %26 to i8*
      %locVal107 = load volatile i32, i32* %loc, align 4
      %owner.0.owner.0.owner.0.owner.0.ownerVal108 = load volatile i32, i32* %owner, align 4
      %28 = call i1 @sync_slowpath(i32 %locVal107, i32 %owner.0.owner.0.owner.0.owner.0.ownerVal108, i8* %27) #19
      br i1 %28, label %pre.sync, label %sync.savectx
    */

    B.SetInsertPoint(syncSlowPath);
    // Check if we can resume directly
    /*
    det.cont11.slowPath:                              ; preds = %det.achd10, %det.achd10.slowPath, %det.cont9.tf.slowPath
      ....
      %26 = call i64 @llvm.read_register.i64(metadata !3)
      %27 = inttoptr i64 %26 to i8*
      %locVal107 = load volatile i32, i32* %loc, align 4
      %owner.0.owner.0.owner.0.owner.0.ownerVal108 = load volatile i32, i32* %owner, align 4
      %28 = call i1 @sync_slowpath(i32 %locVal107, i32 %owner.0.owner.0.owner.0.owner.0.ownerVal108, i8* %27) #19
      br i1 %28, label %pre.sync, label %sync.savectx
    */
    Value* mySP = getSP(B, F);
    mySP = B.CreateCast(Instruction::IntToPtr, mySP, IntegerType::getInt8Ty(C)->getPointerTo());
    Value * locVal = B.CreateLoad(Int32Ty, locAlloc, 1, "locVal");
    Value * ownerVal = B.CreateLoad(Int32Ty, ownerAlloc, 1, "ownerVal");
    FunctionCallee sync_slowpath = Get_sync_slowpath(*M);
    auto canResume = B.CreateCall(sync_slowpath, {locVal, ownerVal, mySP});
    auto canResume2 = B.CreateICmpEQ(canResume, B.getInt1(1));
    B.CreateCondBr(canResume2, syncSucc, syncSaveCtxBB);

    B.SetInsertPoint(syncSaveCtxBB);

    // If cannot resume directly, prepare resume ctx
    /*
    sync.savectx:                                     ; preds = %pfor.cond.cleanup.ls1.slowPath
      %23 = call i8** @get_stacklet_ctx() #19
      %24 = call i8** @get_workcontext(i8** %23) #19
      %25 = bitcast i8** %24 to i8*
    */

    // Get ctx from rsp
    FunctionCallee GetWorkCtxFcnCall = Get_get_workcontext(*M);
    FunctionCallee GetStackletCtxFcnCall = Get_get_stacklet_ctx(*M);
    Value* workCtx = B.CreateCall(GetStackletCtxFcnCall);
    Value* workCtx2 = B.CreateCall(GetWorkCtxFcnCall, {workCtx});

    /*
    sync.savectx:                                     ; preds = %pfor.cond.cleanup.ls1.slowPath
      ...
      call void @llvm.uli.save.context.nosp(i8* %25, i8* null)
      multiretcall void @llvm.donothing()
      to label %sync.resume.to.scheduler [label %pre.sync ]
    */

    // Save resume ctx
    auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);
    auto saveContextNoSP = Intrinsic::getDeclaration(M, Intrinsic::uli_save_context_nosp);
    CallInst* result = B.CreateCall(saveContextNoSP, {B.CreateBitCast(workCtx2, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});
    B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), syncRuntimeBB, {syncSucc}, {});
    syncSlowPath->eraseFromParent();

    // Pass control to the scheduler
    /*
    sync.resume.to.scheduler:                         ; preds = %sync.savectx
      %26 = getelementptr i8*, i8** %24, i64 1
      store i8* blockaddress(@startup_cilk.outline_pfor.cond.ls1, %sync.savectx) successor  i32 1, i8** %26, align 8
      %27 = getelementptr i8*, i8** %23, i64 18
      %28 = load i8*, i8** %27, align 8
      call void @resume2scheduler(i8** %24, i8* %28) #19
      unreachable
    */

    // Create a basic block that performs the synchronization
    B.SetInsertPoint(syncRuntimeBB);
    Value* savedPc = B.CreateConstGEP1_32(VoidPtrTy, workCtx2, 1); //void** (no loading involved)

    // Save resume point
    /*
    sync.resume.to.scheduler:                         ; preds = %sync.savectx
      store i8* blockaddress(@startup_cilk.outline_pfor.cond.ls1, %sync.savectx) successor  i32 1, i8** %26, align 8
      ...
    */
    B.CreateStore(BlockAddress::get(syncSaveCtxBB, 1), savedPc);

    // Resume to the scheduler
    /*
    sync.resume.to.scheduler:                         ; preds = %sync.savectx
      ....
      %27 = getelementptr i8*, i8** %23, i64 18
      %28 = load i8*, i8** %27, align 8
      call void @resume2scheduler(i8** %24, i8* %28) #19
      unreachable
    */
    Value* newsp = B.CreateConstGEP1_32(VoidPtrTy, workCtx, 18);
    newsp = B.CreateLoad(VoidPtrTy, newsp);
    FunctionCallee resume2scheduler = Get_resume2scheduler(*M);
    auto ci = B.CreateCall(resume2scheduler, {workCtx2, newsp});
    Function* fcn = ci->getCalledFunction();
    fcn->addFnAttr(Attribute::NoReturn);
    B.CreateUnreachable();


    // Fix Phi node since using direct resume, the pre.Sync will have at least two predecessor
    // direct resume allow the slowpath to directly execute the fast path without going through the scheduler
    /*
      in rectmul.cpp
      %b.0.slowPath = phi i32 [ %call7.slowPath, %det.cont.slowPath ], [ %call16.slowPath, %det.cont11.slowPath ]
      to
      %b.0.slowPath = phi i32 [ %call7.slowPath, %det.cont.slowPath ], [ %call16.slowPath, %det.cont11.slowPath ], [ %call7.slowPath, %sync.resume.to.scheduler ], [ %call16.slowPath, %sync.resume.to.scheduler2 ]
    */
    for (auto& ii : *syncSucc) {
      // Look for phi node in the successor of a sync inst
      if(isa<PHINode>(&ii)) {
        PHINode* phiN = dyn_cast<PHINode>(&ii);
        unsigned incomingPair = phiN->getNumIncomingValues();
        Value * inst2copy = nullptr;
	// Look for incoming blcok from syncBBSlowPath (share the same incoming value with syncSaveCtxBB)
        for(unsigned i = 0; i<incomingPair; i++)  {
          BasicBlock* incomingBB = phiN->getIncomingBlock(i);
          if ( incomingBB == syncBBSlowPath ) {
            inst2copy = (phiN->getIncomingValue(i));
          }
        }
	// Update phi node to include syncSaveCtxBB as one of its predecessor
        if(inst2copy) {
          phiN->addIncoming(inst2copy, syncSaveCtxBB);
        }
      }
    }

  }
  return;
}

void LazyDTransPass::instrumentMainFcn(Function& F) {
  // Initialize the PRSC at the beginning of main
  Module* M = F.getParent();
  IRBuilder<> B(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

  FunctionCallee INITWORKERS_ENV = Get_initworkers_env(*M);
  FunctionCallee DEINITWORKERS_ENV = Get_deinitworkers_env(*M);
  FunctionCallee INITPERWORKERS_SYNC = Get_initperworkers_sync(*M);
  FunctionCallee DEINITPERWORKERS_SYNC = Get_deinitperworkers_sync(*M);

  Value* ONE = B.getInt32(1);
  Value* ZERO = B.getInt32(0);

  B.CreateCall(INITWORKERS_ENV);
  B.CreateCall(INITPERWORKERS_SYNC,  {ZERO, ONE});

  for (auto &BB : F){
    Instruction * termInst = BB.getTerminator();
    if(isa<ReturnInst>(termInst)){
      B.SetInsertPoint(termInst);
      B.CreateCall(DEINITPERWORKERS_SYNC, {ZERO, ONE});
      B.CreateCall(DEINITWORKERS_ENV);
    }
  }
}


// Do some initialization
bool LazyDTransPass::runInitialization(Module &M) {
  // Create a new function needed for this Module
  auto * fcn = UNWINDRTS_FUNC(unwind_gnuhash, M);
  fcn->addFnAttr(Attribute::NoUnwindPath);
  fcn = UNWINDRTS_FUNC(unwind_queryunwindaddress, M);
  fcn->addFnAttr(Attribute::NoUnwindPath);

#ifdef OPTIMIZE_UNWIND
  fcn->addFnAttr(Attribute::NoInline);
#endif

  // Create the structure for request and response channel
  // Copied from CilkABI.cpp
  LLVMContext &C = M.getContext();
  Type *VoidPtrTy = Type::getInt8PtrTy(C);
  Type *Int64Ty = Type::getInt64Ty(C);
  Type *Int32Ty = Type::getInt32Ty(C);
  Type *Int16Ty = Type::getInt16Ty(C);
  Type *Int8Ty  = Type::getInt8Ty(C);

  // Get or create local definitions of Cilk RTS structure types.
  RequestChannelTy = StructType::lookupOrCreate(C, "struct._request_channel");
  ResponseChannelTy = StructType::lookupOrCreate(C, "struct._response_channel");

  if (RequestChannelTy->isOpaque()) {
    RequestChannelTy->setBody(
                              Int32Ty,                     // senderThreadId
                              ArrayType::get(Int8Ty, 2),   // padding_char
                              Int8Ty,                      // potentialParallelTask
                              Int8Ty,                      // inLoop
                              ArrayType::get(Int64Ty, 31)  // padding
                              );
  }

  if (ResponseChannelTy->isOpaque())
    ResponseChannelTy->setBody(
                               Int32Ty,
                               Int8Ty,
                               Int8Ty,
                               ArrayType::get(Int8Ty, 250)
                               );


  if(fcn)
    return true;

  return false;
}


// We don't modify the program, so we preserve all analyses
void LazyDTransPass::runAnalysisUsage(AnalysisUsage &AU) const  {
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<DominanceFrontierWrapperPass>();
}

static unsigned getInstructionCount(Function &F) {
  unsigned NumInstrs = 0;
  for (const BasicBlock &BB : F)
    NumInstrs += std::distance(BB.begin(), BB.end());

  return NumInstrs;
}

bool LazyDTransPass::runImpl(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT,  DominanceFrontier &DF, LoopInfo &LI)  {
  if(F.getName() == "main") {
    errs() << "Source filename: " << F.getParent()->getSourceFileName() << "\n";
    if(EnableMainInstrumentation)
      /*
	define dso_local noundef i32 @main(i32 noundef %argc, i8** nocapture noundef readonly %argv) local_unnamed_addr #4 {
	entry:
	  call void @initworkers_env() #12
	  call void @initperworkers_sync(i32 0, i32 1) #12
          ....
          ....
          ....
        for.cond.cleanup:
          call void @deinitperworkers_sync(i32 0, i32 1) #12
	  call void @deinitworkers_env() #12
	  ret i32 0
       */
      instrumentMainFcn(F);

    // Don't insert polling in the main function since the scheduler have not been initialized yet.
    F.addFnAttr(Attribute::ULINoPolling);

    // Should not be an issue?
    for(auto &BB : F) {
      for(auto &II : BB) {
        if (isa<DetachInst>(&II)) {
          errs() << "Warning,detach inside main\n";
        }
      }
    }
  }

#if 0
  // qsort will generate an error without this
  if(F.getName().contains(F.getParent()->getSourceFileName())) {
    F.addFnAttr(Attribute::NoUnwindPath);
  }
#endif

  // Delete task.frame.create and task.frame.use for now
  SmallVector<IntrinsicInst*, 4 > taskframe2delete;
  for(auto &BB : F) {
    for(auto &I : BB) {
      if (IntrinsicInst *II = dyn_cast<IntrinsicInst>(&I)) {
        if ( Intrinsic::taskframe_use == II->getIntrinsicID()) {
          taskframe2delete.push_back(II);
        }
      }
    }
  }
  for(auto ii : taskframe2delete) {
    ii->eraseFromParent();
  }

  // Check if a function is a forking / spawning function or not
  bool bHavePforHelper = false;
  bHaveDynamicAlloca = false;
  bHaveCallFcn6Args = false;
  bHaveFork = F.getFnAttribute("poll-at-loop").getValueAsString()=="true";
  if(!bHaveFork) {
    for(auto &BB : F) {
      for(auto &II : BB) {
        if (isa<DetachInst>(&II)) {
          bHaveFork = true;
        }
        if (isa<AllocaInst>(&II)) {
          bHaveDynamicAlloca = true;
        }
        if( isa<CallInst>(&II) ) {
          bHaveCallFcn6Args = (dyn_cast<CallInst>(&II)->arg_end() - dyn_cast<CallInst>(&II)->arg_begin() > 6);

          CallInst* ci = dyn_cast<CallInst>(&II);
          Function* fcn = ci->getCalledFunction();

          if(fcn && fcn->getFnAttribute("poll-at-loop").getValueAsString()=="true"){
            bHavePforHelper=true;
          }
        }
      }
    }
  }

  // Attempt to optimize frame pointer, turn of currently
#ifdef OPTIMIZE_FP
  if(bHaveFork || bHaveCallFcn6Args) {
#else
  if(true) {
#endif
    F.addFnAttr("no-frame-pointer-elim");
    F.addFnAttr("no-frame-pointer-elim-non-leaf");
    F.addFnAttr("no-realign-stack");
  }

  // If function does not have a fork and instruction is less than MaxInstPoll
  // Default value of MaxInstPoll=1
  if(!bHaveFork && getInstructionCount(F) <= MaxInstPoll)
    F.addFnAttr(Attribute::ULINoPolling);

  // Do not process function that have the nounwindpath attribute
  if(F.hasFnAttribute(Attribute::NoUnwindPath)) {
    // Before simply returning, lower tapir grainsize if it has any
    SmallVector<IntrinsicInst*, 4 > ii2delete;
    for(auto &BB : F) {
      for(auto &II : BB) {
        if (IntrinsicInst *IntrinsicI = dyn_cast<IntrinsicInst>(&II)) {
          // lower grainsize
          if (Intrinsic::tapir_loop_grainsize == IntrinsicI->getIntrinsicID()){
            ii2delete.push_back(IntrinsicI);
            lowerGrainsizeCall(IntrinsicI);
          }
        }
      }
    }
    for(auto ii : ii2delete) {
      ii->eraseFromParent();
    }
    return false;
  }

  // If function does not return (simply abort), do not process
  // Are there such cases?
  bool bNotProcess = true;
  for(auto &BB : F) {
    if (isa<ReturnInst>(BB.getTerminator())) {
      bNotProcess = false;
    }
  }
  if(bNotProcess) return false;

  // Perform static analysis on the Detach-Reattach IR
  LiveVariable LV;
  ReachingDetachInst RDI;
  ReachingStoreReachableLoad RSI;

  // Run Live Variable, Reaching Detach, and Reaching Store
  LV.recalculate(F);
  RDI.recalculate(F, AM, DT, LI);
  RSI.recalculate(F, AM, DT, LI);

  // Based on DFA, bad idea, should just use SSA based.
  auto  &LVin = LV.getLiveInInstBBMap();
  auto  &LVout = LV.getLiveOutInstBBMap();

  // Similar to Reaching Definition
  auto  &RDIPath = RDI.getReachingDetachPathMap();
  auto  &RSIPath = RDI.getReachingSyncPathMap();
  auto  &MapBB2InVal = RDI.getMapBB2InVal();
  auto  &RDIBB = RDI.getReachingDetachBBMap();

  auto  &RSBB = RSI.getReachingStore();

  // Get order of update. SeqOrder and looporder contains the Detach Instruction's Parent (detach's basic block)
  auto  &seqOrder = RDI.getSeqOrderInst();
  auto  &loopOrder = RDI.getLoopOrderInst();

  // The phi node needed in the continuation in slow path (Key: Detach inst. Value: Live variables defined in between detach inst).
  SmallPtrSet<Instruction*, 8> RequiredPhiNode;
  SmallPtrSet<Instruction*, 8> PhiNodeInserted;

  // Map fast path BB and inst to slow path BB and inst
  ValueToValueMapTy VMapSlowPath;
  // Reverse of VMapSlowPath
  ValueToValueMapTy VMapSlowPathReverse;
  // Map fast path BB and inst to got stolen handler path BB inst
  ValueToValueMapTy VMapGotStolenPath;

  // Map Detach inst to an alloca inst that store the spawn result (if any)
  DenseMap <DetachInst*, AllocaInst*> DetachToAllocaMap;
  // Key: Detach inst ; Value: alloca inst that reaches it
  DenseMap <DetachInst*, SmallPtrSet<AllocaInst*, 8>> ReachingAllocSet;
  // Store all the alloca that stores the fork result
  SmallPtrSet<AllocaInst*, 8> AllocaSet;
  // Store all the multiretcall that can be transformed into branch based on path
  SmallPtrSet<MultiRetCallInst*, 8> MultiRetCallPathSet;

  // The original basic block that needs to be cloned.
  SmallVector<BasicBlock*, 8> bb2clones;
  for( auto &BB : F ) {
    bb2clones.push_back(&BB);
  }

  // Store the Instruction and BB that represent the sync instruction
  SmallVector<BasicBlock*, 8> syncBBs;
  SmallVector<SyncInst*, 8> syncInsts;
  for( auto pBB : bb2clones ) {
    if(isa<SyncInst>( pBB->getTerminator())) {
      syncBBs.push_back(pBB);
      syncInsts.push_back(dyn_cast<SyncInst>( pBB->getTerminator()));
    }
  }

  // Add attribute to function that contains a detach or within a detached basic block
  for (auto pBB : bb2clones){
    if (DetachInst * DI = dyn_cast<DetachInst>(pBB->getTerminator())){
      F.addFnAttr(Attribute::Stealable);
      F.addFnAttr(Attribute::Forkable);
      BasicBlock * detachBlock = dyn_cast<DetachInst>(DI)->getDetached();
      for( Instruction &II : *detachBlock ) {
	if( isa<CallInst>(&II) ) {
	  dyn_cast<CallInst>(&II)->getCalledFunction()->addFnAttr(Attribute::Forkable);
	  dyn_cast<CallInst>(&II)->getCalledFunction()->addFnAttr(Attribute::ReturnsTwice);
	}
      }
    }
  }

  // Map detach to alloca it stores to, map detach to alloca that reaches it, map detach and alloca to latest store to that alloca that reaches detach
  for (auto pBB : bb2clones) {
    if(isa<DetachInst>( pBB->getTerminator() )) {
      DetachInst* di = dyn_cast<DetachInst>(pBB->getTerminator());
      BasicBlock* detachedBB = di->getDetached();

      // Look for the store inst
      for(auto& ii: *detachedBB) {
        // Map Detach inst to an alloca inst that store the spawn result (if any)
        if (isa<StoreInst>(&ii)) {
          StoreInst* si = dyn_cast<StoreInst> (&ii);
          AllocaInst* ai = dyn_cast<AllocaInst>(si->getPointerOperand());
          // Only if it is an alloca instruction
          if(!ai) continue;
          DetachToAllocaMap[di] = ai;
          AllocaSet.insert(ai);
	  // Currently not used
          // Set it to a fork storage
          ai->setForkStorage(true);
        }
      }
    }
  }

  // TODO: Can be optimize, store detach in vector
  for (auto pBB : bb2clones) {
    if(isa<DetachInst>( pBB->getTerminator() )) {
      DetachInst* di = dyn_cast<DetachInst>(pBB->getTerminator());
      BasicBlock* detachedBB = di->getDetached();

      auto& reachingStore = RSBB[di->getParent()];
      for (auto potAllocaInst : reachingStore) {
        AllocaInst* ai = dyn_cast<AllocaInst>(potAllocaInst);
        if(ai && AllocaSet.find(ai) != AllocaSet.end()) {
          // If it is an alloca inst
          if(DetachToAllocaMap[di])
            if(DetachToAllocaMap[di] == ai)
              continue;
          ReachingAllocSet[di].insert(ai);
        } else {
          // If the definition uses one of the alloca variable
          unsigned nOp = potAllocaInst->getNumOperands();
          for (unsigned i = 0; i<nOp; i++) {
            auto opVal = potAllocaInst->getOperand(i);
            AllocaInst* ai2 = dyn_cast<AllocaInst>(opVal);
            if(ai2 && AllocaSet.find(ai2) != AllocaSet.end()) {
              if(DetachToAllocaMap[di])
                if(DetachToAllocaMap[di] == ai2)
                  continue;
              ReachingAllocSet[di].insert(ai2);
            }
          }
        }
      }
    }
  }

  // Find multiretcall that can be converted into branch based on the path
  for (auto pBB : bb2clones) {
    if(isa<MultiRetCallInst>( pBB->getTerminator() )) {
      MultiRetCallPathSet.insert(dyn_cast<MultiRetCallInst>(pBB->getTerminator()));
    }
  }

  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // Instrument prologue and epilogue to insert parallel runtime call
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  const DataLayout &DL = M->getDataLayout();
  // Potential Jump Fcn
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::uli_potential_jump);
  IRBuilder<> B(C);

  //===================================================================================================

  // Create memory to store location of parallel task in workctx_ar
  B.SetInsertPoint(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

  for(auto& II: F.getEntryBlock()) {
    if (!isa<AllocaInst>(&II)) {
      B.SetInsertPoint(&II);
      break;
    }
  }

  Type *Int64Ty = Type::getInt64Ty(C);
  Type *Int32Ty = Type::getInt32Ty(C);
  Type *Int1Ty  = Type::getInt1Ty(C);
  Type *VoidTy  = Type::getVoidTy(C);

  // Location of the work
  Value* locAlloc = B.CreateAlloca(Int32Ty, DL.getAllocaAddrSpace(), nullptr, "loc");
  Value* insertPoint  = locAlloc;

  // Indicate that we arrive at the cont path from the the detach block instead from the runtime
  Value* fromSlowPathAlloc  = B.CreateAlloca(Int32Ty, DL.getAllocaAddrSpace(), nullptr, "fromSlowPath");
  insertPoint  = fromSlowPathAlloc;

  // The owner of the work
  Value* ownerAlloc = B.CreateAlloca(Int32Ty, DL.getAllocaAddrSpace(), nullptr, "owner");
  insertPoint = ownerAlloc;

  Value* bHaveUnwindAlloc = nullptr;
  if(EnableUnwindOnce) {
    // Create memory to store haveBeenUnwind
    bHaveUnwindAlloc = B.CreateAlloca(Int1Ty, DL.getAllocaAddrSpace(), nullptr, "bHaveUnwind");
    if (DisableUnwindPoll || !bHaveFork)
      insertPoint = bHaveUnwindAlloc;
    else
      insertPoint = B.CreateStore(B.getInt1(0), bHaveUnwindAlloc);
  }


#if 0
  // TODO: Do this on the basic block of the fork?
  //if(bHaveFork && !(F.getFnAttribute("poll-at-loop").getValueAsString()=="true") && !bHavePforHelper) {
  if(bHaveFork && !(F.getFnAttribute("poll-at-loop").getValueAsString()=="true")) {
  //if(bHaveFork) {
    GlobalVariable* prequestcell = GetGlobalVariable("request_cell", ArrayType::get(Int64Ty, 32), *M, true);
    Value* L_ONE = B.getInt64(1);
    auto workExists = B.CreateConstInBoundsGEP2_64(ArrayType::get(Int64Ty, 32), prequestcell, 0, 1 );
    insertPoint = B.CreateStore(L_ONE, workExists);
  }

#else

  GlobalVariable* prequestcell = GetGlobalVariable("request_cell", ArrayType::get(IntegerType::getInt64Ty(C), 32), *M, true);
  GlobalVariable* reqlocal = GetGlobalVariable("req_local", RequestChannelTy, *M, true);

  Value* L_ONE = B.getInt64(1);
  auto workExists = B.CreateConstInBoundsGEP2_64(ArrayType::get(IntegerType::getInt64Ty(C), 32), prequestcell, 0, 1 );

  // Store one to potential parallel task flag
  for(auto elem: RDIPath) {
    DetachInst * DI = elem.first;
    BasicBlock * parent = DI->getParent();

    // If loop, insert it in the preheader
    bool skipLoop = false;
    for (auto L : LI) {
      if(L->contains(DI)) {
        if(L->getLoopPreheader())
          B.SetInsertPoint(L->getLoopPreheader()->getTerminator());
        else
          B.SetInsertPoint(L->getHeader()->getTerminator());
#ifdef USE_CHANNEL
        if(!DisableUnwindPoll)
          StoreSTyField(B, DL, RequestChannelTy,
                        B.getInt8(1),
                        reqlocal, RequestChannelFields::potentialParallelTask, /*isVolatile=*/false,
                        AtomicOrdering::NotAtomic);
#else
        B.CreateStore(L_ONE, workExists);
#endif
        skipLoop = true;
      }
    }

    if (skipLoop)
      continue;

    // Get any basic block from a detach point that can reach this continuation
    auto reachingBB = elem.second;
    // Get the predecessor
    for( pred_iterator PI = pred_begin(parent); PI != pred_end(parent); PI++ ) {
      BasicBlock* pred = *PI;
      // Check if predecessor is not in the reachingBB
      if(reachingBB.find(pred) == reachingBB.end()) {
        B.SetInsertPoint(pred->getTerminator());
#ifdef USE_CHANNEL
        if(!DisableUnwindPoll)
          StoreSTyField(B, DL, RequestChannelTy,
                      B.getInt8(1),
                      reqlocal, RequestChannelFields::potentialParallelTask, /*isVolatile=*/false,
                      AtomicOrdering::NotAtomic);
#else
        B.CreateStore(L_ONE, workExists);
#endif
      }
    }
  }

#endif

  // Stores the workcontext value from the slow path entry and will be used to rematerialze the work context in the slowpath
  SSAUpdater SSAUpdateWorkContext;

  // Create the slow path (inserting phi node to capture data from fast path, renaming slow path variable with phi node or fast path variable if needed)
  DenseMap<BasicBlock*, BasicBlock*> syncBB2syncPred;
  if (!seqOrder.empty() || !loopOrder.empty()) {

    //-------------------------------------------------------------------------------------------------
    // If the detach inst has the function inlined, create a wrapper function for it.
    generateWrapperFuncForDetached(F, seqOrder, loopOrder, LVin);

    //-------------------------------------------------------------------------------------------------
    // TODO: If there is recursive sync, create a wrapper for each sync. Doest not work, to complicated, might as well create a new pass before this.

    //-------------------------------------------------------------------------------------------------
    // Find the live varaible required in each slow path-continuation to construct the phi nodes needed
    // This done by intersecting all live IN instruction in the continuation with the
    // variables defined in basic block that can reach the continuation from any previous possible detach inst.
    findRequiredPhiNodes(RDIPath, RSIPath, MapBB2InVal, LVin, syncInsts, RequiredPhiNode);

    //-------------------------------------------------------------------------------------------------
    // Perform the cloning
    // Push the original basic block
    cloneBasicBlock(F, bb2clones, VMapSlowPath, VMapSlowPathReverse, AllocaSet);

    //-------------------------------------------------------------------------------------------------
    // Add potential jump to the slow path continuation
    addPotentialJump(F, seqOrder, loopOrder, VMapSlowPath, fromSlowPathAlloc, SSAUpdateWorkContext, ReachingAllocSet, DT);

    // Merge slow path into fast path
    for(auto syncBBi = syncInsts.begin(); syncBBi != syncInsts.end() ; syncBBi++ ) {
      // Merge slow path to fast path
      auto syncInst = *syncBBi;
      auto syncBB = syncInst->getParent();
      auto syncParent = syncInst->getParent();
      auto syncSucc = syncInst->getSuccessor(0);
      //auto syncSuccSlow = dyn_cast<BasicBlock>(VMapSlowPath[syncSucc]);
      auto syncInstSlow = dyn_cast<SyncInst>(VMapSlowPath[syncInst]);
      auto syncSuccSlow = syncInstSlow->getSuccessor(0);

      assert(syncSuccSlow && "Sync's successor in slow path must exists");
      assert(syncInstSlow && "Sync instruction in slow path must exists");

      // Jump to sync succ
      if(!syncBB2syncPred.count(syncSucc)) {
        BasicBlock* syncSuccPre = BasicBlock::Create(C, "pre.sync", &F);
        B.SetInsertPoint(syncSuccPre);
        B.CreateStore(B.getInt1(0), bHaveUnwindAlloc);
        B.CreateBr(syncSucc);
        syncBB2syncPred[syncSucc] = syncSuccPre;

        B.SetInsertPoint(syncSuccPre->getTerminator());
      }

      // Remove the phi node in the original successor
      SmallVector<PHINode*, 4> phiInstVec;
      for(auto &ii : *syncSuccSlow) {
        if(PHINode* phiInst = dyn_cast<PHINode>(&ii)) {
          phiInstVec.push_back(phiInst);
        }
      }
      for(auto phiInst : phiInstVec) {
        unsigned incomingPair = phiInst->getNumIncomingValues();
        for(unsigned i = 0; i<incomingPair; i++)  {
          BasicBlock* incomingBB = phiInst->getIncomingBlock(i);
          if(incomingBB == syncInstSlow->getParent()) {
            // Remove the incoming block and its value
            phiInst->removeIncomingValue(incomingBB);
          }
        }
      }

      // Merge the slow path back to fast path
      syncInstSlow->setSuccessor(0, syncBB2syncPred[syncSucc]);
    }

    //-------------------------------------------------------------------------------------------------
    // Create the gotstolen handler
    createGotStolenHandler(seqOrder, loopOrder, locAlloc, ownerAlloc, LVout, LVin, VMapSlowPath, VMapGotStolenPath);

    //====================================================================================================

    // DT Analysis
    //-------------------------------------------------------------------------------------------------
    // Recalculate DT and DF after cloning
    DT.recalculate(F);
    DF.analyze(DT);
    //-------------------------------------------------------------------------------------------------
    // Reconstruct SSA
    DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>> phiMap;
    updateSlowVariables_2(F, VMapSlowPathReverse, VMapSlowPath, syncBB2syncPred, DT, DF, phiMap, RequiredPhiNode, PhiNodeInserted, LVin, seqOrder, loopOrder, syncInsts);
  }

  // Merge back the slow path back the fast path
  //---------------------------------------------------
  // Get all the detach inst in bbOrder
  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  //-------------------------------------------------------------------------------------------------
  // Multiretcall pathdependent that is in fast path is converted as branch to default, while in slowpath is converted as branch to first indirect bb
  for(auto mrc: MultiRetCallPathSet) {
    // TODO: CNP If not part of the parallel path, ignore
    if(!VMapSlowPath[mrc])
      continue;

    auto mrcSlowpath = dyn_cast<MultiRetCallInst>(VMapSlowPath[mrc]);

    BasicBlock* defaultDestFast = mrc->getDefaultDest();
    BasicBlock* indirectDestFast = mrc->getIndirectDest(0);

    BasicBlock* defaultDestSlow = mrcSlowpath->getDefaultDest();
    BasicBlock* indirectDestSlow = mrcSlowpath->getIndirectDest(0);

    mrcSlowpath->setDefaultDest(indirectDestSlow);
    mrcSlowpath->setIndirectDest(0, defaultDestSlow);


  }

  //-------------------------------------------------------------------------------------------------
  // Parallelize Fcn
  // Add runtime to parallelize fcn
  instrumentSlowPath(F, seqOrder, loopOrder, locAlloc, ownerAlloc, bHaveUnwindAlloc, fromSlowPathAlloc, syncInsts, VMapSlowPath, RDIBB, SSAUpdateWorkContext);

  // Modify fast path
  //=================================================================================================
  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  // Create Unwind Path first
  BasicBlock * unwindPathEntry = createUnwindHandler(F, locAlloc, ownerAlloc, bHaveUnwindAlloc, bbOrder, VMapSlowPath, VMapGotStolenPath);
  SmallVector<BasicBlock*, 4> bbList = {unwindPathEntry};
  Value* insertPointEnd = nullptr;
#if 0
  // Move multiretcall only after all the alloca at the prolog
  while (isa<AllocaInst>(dyn_cast<Instruction>(insertPoint)->getNextNode())) {
    insertPoint = dyn_cast<Instruction>(insertPoint)->getNextNode();
  }
  auto afterBB = insertPotentialJump(dyn_cast<Instruction>(insertPoint), bbList);

  // Fixme: Hack
  for (Function::const_arg_iterator J = F.arg_begin(); J != F.arg_end(); ++J) {
    if(J->hasStructRetAttr()){
      IRBuilder<> B(dyn_cast<Instruction>(insertPoint)->getNextNode());
      //using AsmTypeCallee = void (void);
      FunctionType *killCallee = FunctionType::get(VoidTy, {VoidTy}, false);
      InlineAsm* Asm = InlineAsm::get(killCallee, "", "~{rbx},~{r10},~{r11},~{r12},~{r13},~{r14},~{r15},~{rdi},~{rsi},~{r8},~{r9},~{rdx},~{rcx},~{rax},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
      B.CreateCall(Asm);
      break;
    }
  }
#else
  // Insert multiretcall to uwnind_path_entry just before epilog. This should be better than in prolog since
  // there might be stack spilling if placed after prolog.
  for (auto pBB : bb2clones) {
    Instruction * termInst = pBB->getTerminator();
    if(isa<ReturnInst>(termInst)){
      auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);
      IRBuilder<> B(termInst);
      // Ensure that the return instruction in a basicblock has a previous node (not a single instruction inside a basicblock)
      B.CreateCall(dyn_cast<Function>(donothingFcn),{});
      assert(termInst->getPrevNode() && "Return inst has not prev node");
      insertPointEnd = termInst->getPrevNode();
      break;
    }
  }
  assert(insertPointEnd && "Function has no return inst");
  // Can cause performance improvement on classify - kddcup if turn off
  auto afterBB = insertPotentialJump(dyn_cast<Instruction>(insertPointEnd), bbList);

  // Fixme: Hack
  for (Function::const_arg_iterator J = F.arg_begin(); J != F.arg_end(); ++J) {
    if(J->hasStructRetAttr() || F.getReturnType()->isStructTy()){
      IRBuilder<> B(dyn_cast<Instruction>(insertPointEnd)->getNextNode());
      //using AsmTypeCallee = void (void);
      FunctionType *killCallee = FunctionType::get(VoidTy, {}, false);
      InlineAsm* Asm = InlineAsm::get(killCallee, "", "~{rbx},~{r10},~{r11},~{r12},~{r13},~{r14},~{r15},~{rdi},~{rsi},~{r8},~{r9},~{rdx},~{rcx},~{rax},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
      B.CreateCall(Asm);
      break;
    }
  }
#endif

#ifdef LAZYD_POLL
  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // Instrument prologue and epilogue to insert parallel runtime call
  B.SetInsertPoint(dyn_cast<Instruction>(insertPoint)->getNextNode());

  // Insert poling
  // Polling @prologue
  if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) && !(F.getFnAttribute("poll-at-loop").getValueAsString()=="true") ) {
    Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::uli_unwind_poll);
    //pollFcn->addFnAttr(Attribute::Forkable);
    auto res = B.CreateCall(pollFcn);
    //res->setTailCall(true);
    LLVM_DEBUG(dbgs() << F.getName() << " : Polling at prologue\n");
  }

  // Polling @epilogue
  for (auto pBB : bb2clones){
    Instruction * termInst = pBB->getTerminator();
    if(isa<ReturnInst>(termInst) ){
      B.SetInsertPoint(termInst);

      if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
        Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::uli_unwind_poll);
        //pollFcn->addFnAttr(Attribute::Forkable);
        if(EnableProperPolling >= 1 ) {
          auto res = B.CreateCall(pollFcn);
          res->setTailCall(true);
          LLVM_DEBUG(dbgs() << F.getName() << " : Polling at epilogue\n");
        }
      }
    }
  }

  // Polling @loop
  if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
    // Insert Poll in looping
    for (auto L : LI) {
      if(EnableProperPolling >= 2 || F.getFnAttribute("poll-at-loop").getValueAsString()=="true") {
        insertPollingAtLoop(*L, unwindPathEntry, bHaveUnwindAlloc);
      }
    }
  }
#endif
  //-------------------------------------------------------------------------------------------------
  // .clear() somehow is needed to remove assertion
  RequiredPhiNode.clear();
  RDIPath.clear();
  RDIBB.clear();
  RSIPath.clear();
  PhiNodeInserted.clear();

  // Convert DetachInst, ReattachInst, and SyncInst in the fast path to branch
  convertTapirIrToBr(F);

  //-------------------------------------------------------------------------------------------------
  // Post process: Simplify CFG and verify function
  postProcessCfg(F, AM, DT, AllocaSet);

  // Lower the grainsize or unwind poll pfor
  SmallVector<IntrinsicInst*, 4 > ii2delete;
  for(auto &BB : F) {
    for(auto &II : BB) {
      if (IntrinsicInst *IntrinsicI = dyn_cast<IntrinsicInst>(&II)) {
        // lower grainsize
        if (Intrinsic::tapir_loop_grainsize == IntrinsicI->getIntrinsicID()){
          ii2delete.push_back(IntrinsicI);
          lowerGrainsizeCall(IntrinsicI);
        } else if(Intrinsic::uli_unwind_poll_pfor == IntrinsicI->getIntrinsicID()) {
          ii2delete.push_back(IntrinsicI);
          Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::uli_unwind_poll_pfor2);
          IRBuilder<> B(IntrinsicI);
          CallInst* call = dyn_cast<CallInst>(&II);
          B.CreateCall(pollFcn, {call->getArgOperand(0),call->getArgOperand(1), call->getArgOperand(2), bHaveUnwindAlloc});
        }
      }
    }
  }
  // Delete the intrinsics
  for(auto ii : ii2delete) {
    ii->eraseFromParent();
  }

  return true;
}


PreservedAnalyses
LazyDTransPass::run(Function &F, FunctionAnalysisManager &AM) {
  // Run on function.
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  // Get Dominance Tree and Dominance Frontier to add extra phi node (fix data flow)
  // and perform renaming on the clone fcn (need to fix SSA)
  DominanceFrontier &DF = AM.getResult<DominanceFrontierAnalysis>(F);
  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);

  runInitialization(*F.getParent());

  bool Changed = runImpl(F, AM, DT, DF, LI);

  if (!Changed)
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  // TODO: what analyses are preserved?
  return PA;
}

namespace llvm {

  //static RegisterPass<LazyDTrans> X("lazyd-trans", "Lazy D Transformation", false, false);

Pass *createLazyDTransPass() {
  return new LazyDTrans();
}

}
