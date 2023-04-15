#define DEBUG_TYPE "lazyd-trans"

#include "llvm/Pass.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/DominanceFrontier.h"
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
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/ULI/LazyDTrans.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

//#include "llvm/Transforms/Utils/Local.h"

#include <iostream>

using namespace llvm;

// Set the size of the work context length
static cl::opt<int> WorkCtxLen(
"lazy-set-workctx-len", cl::init(WORKCTX_SIZE), cl::NotHidden,
  cl::desc("Size of work context length (default=WORKCTX_SIZE)"));

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

// Use builtin to save restore context
static cl::opt<bool> EnableSaveRestoreCtx(
"lazy-enable-saverestore-ctx", cl::init(true), cl::NotHidden,
  cl::desc("Use builtin to save restore context (default = on)"));


// Do not add the push and pop of the seed
static cl::opt<bool> DisablePushPopSeed(
"lazy-disable-pushpop-seed", cl::init(true), cl::NotHidden,
  cl::desc("Do not insert any push and pop of the seed function call (default = on)"));

// Allow removing store/load to/from fork storage
static cl::opt<bool> EnableStoreLoadForkStorage(
"lazy-enable-storeload-forkstorage", cl::init(true), cl::NotHidden,
  cl::desc("Remove store/load to/from fork storage (default = on)"));

// Support only unwinding the same frame once
static cl::opt<bool> EnableUnwindOnce(
"lazy-enable-unwind-once", cl::init(true), cl::NotHidden,
  cl::desc("Enable unwind once for each stack frame (default = on)"));

// Use SSAUpdater to merge back slow path to fast path
static cl::opt<bool> EnableSSAUpdateTransformation(
"lazy-enable-ssaupdate-xform", cl::init(true), cl::NotHidden,
  cl::desc("Use SSAUpdater to transform the detach inst  (default = on)"));

// Use the new IR and constant to see if it is working
static cl::opt<bool> EnableMultiRetIR(
"lazy-enable-multiretir", cl::init(true), cl::NotHidden,
  cl::desc("Use new ir to represent fork'ed function  (default = on)"));

// TODO: http://blog.llvm.org/2011/09/greedy-register-allocation-in-llvm-30.html

// Copied from CilkABI.cpp

using __cilkrts_get_nworkers = int ();

#define CILKRTS_FUNC(name, CGF) Get__cilkrts_##name(CGF)

#define DEFAULT_GET_CILKRTS_FUNC(name)                                  \
  static Function *Get__cilkrts_##name(Module& M) {                     \
						   return cast<Function>(M.getOrInsertFunction(	\
											       "__cilkrts_"#name, \
												 TypeBuilder<__cilkrts_##name, false>::get(M.getContext()) \
												 )); \
						   }

//DEFAULT_GET_CILKRTS_FUNC(get_nworkers)
//#pragma GCC diagnostic ignored "-Wunused-function"
static Function *Get__cilkrts_get_nworkers(Module& M) {
LLVMContext &C = M.getContext();
AttributeList AL;
AL = AL.addAttribute(C, AttributeList::FunctionIndex,
                       Attribute::ReadNone);
// AL = AL.addAttribute(C, AttributeSet::FunctionIndex,
//                      Attribute::InaccessibleMemOnly);
AL = AL.addAttribute(C, AttributeList::FunctionIndex,
                       Attribute::NoUnwind);
Function *F = cast<Function>(
M.getOrInsertFunction(
"__cilkrts_get_nworkers",
  TypeBuilder<__cilkrts_get_nworkers, false>::get(C),
  AL));
return F;
}

#define DEFAULT_GET_LIB_FUNC(name)                                      \
  static Constant *Get_##name(Module& M) {                              \
					  return M.getOrInsertFunction( #name, \
									  TypeBuilder< name##_ty, false>::get(M.getContext()) \
									); \
  }


#define UNWINDRTS_FUNC(name, CGF) Get__unwindrts_##name(CGF)

using unwind_poll_ty = int(void);
using mylongwithoutjmp_callee_ty = void (void**);

using hashGnui_ty = unsigned (unsigned);
DEFAULT_GET_LIB_FUNC(hashGnui)

using mylongjmp_callee_ty = void (void**);
DEFAULT_GET_LIB_FUNC(mylongjmp_callee)

using mysetjmp_callee_ty = int (void**);
DEFAULT_GET_LIB_FUNC(mysetjmp_callee)

using push_ss_ty = void (void *);
DEFAULT_GET_LIB_FUNC(push_ss)

using push_workctx_ty = void (void**, void*);
DEFAULT_GET_LIB_FUNC(push_workctx)

using pop_workctx_ty = void (void**, void*);
DEFAULT_GET_LIB_FUNC(pop_workctx)

using pop_ss_ty = void (void );
DEFAULT_GET_LIB_FUNC(pop_ss)

using suspend2scheduler_ty = void (int, int, int);
DEFAULT_GET_LIB_FUNC(suspend2scheduler)

using resume2scheduler_ty = void (void**, void* );
DEFAULT_GET_LIB_FUNC(resume2scheduler)

using sync_slowpath_ty = char (int, int, void*);
DEFAULT_GET_LIB_FUNC(sync_slowpath)

using can_direct_steal_ty = void ();
DEFAULT_GET_LIB_FUNC(can_direct_steal)

using measure_resume_parent_ty = void (int);
DEFAULT_GET_LIB_FUNC(measure_resume_parent)

using get_workcontext_ty = void** (void** );
DEFAULT_GET_LIB_FUNC(get_workcontext)

using get_workcontext_locowner_ty = void** (int, int, void*);
DEFAULT_GET_LIB_FUNC(get_workcontext_locowner)

using get_stacklet_ctx_ty = void** ();
DEFAULT_GET_LIB_FUNC(get_stacklet_ctx)

using postunwind_ty = void (void );
DEFAULT_GET_LIB_FUNC(postunwind)

using preunwind_steal_ty = void (void );
DEFAULT_GET_LIB_FUNC(preunwind_steal)

using postunwind_steal_ty = void (void );
DEFAULT_GET_LIB_FUNC(postunwind_steal)

using unwind_suspend_ty = void (void );
DEFAULT_GET_LIB_FUNC(unwind_suspend)

using unwind_workexists_ty = int (void );
DEFAULT_GET_LIB_FUNC(unwind_workexists)

using initialize_parallel_ctx_ty = void (void**, void*, void*);
DEFAULT_GET_LIB_FUNC(initialize_parallel_ctx)

using unwind_gosteal_ty = void (void );
DEFAULT_GET_LIB_FUNC(unwind_gosteal)

using isunwind_triggered_ty = int (void);
DEFAULT_GET_LIB_FUNC(isunwind_triggered)

using initiate_unwindstack_ty = void (void);
DEFAULT_GET_LIB_FUNC(initiate_unwindstack)

using initworkers_env_ty = void (void );
DEFAULT_GET_LIB_FUNC(initworkers_env)

using deinitworkers_env_ty = void (void );
DEFAULT_GET_LIB_FUNC(deinitworkers_env)

using deinitperworkers_sync_ty = void(int, int);
DEFAULT_GET_LIB_FUNC(deinitperworkers_sync)

using initperworkers_sync_ty = void(int, int);
DEFAULT_GET_LIB_FUNC(initperworkers_sync)

namespace {

  GlobalVariable* GetGlobalVariable(const char* GlobalName, Type* GlobalType, Module& M, bool localThread=false){
    GlobalVariable* globalVar = M.getNamedGlobal(GlobalName);
    if(globalVar){
      return globalVar;
    }
    globalVar = dyn_cast<GlobalVariable>(M.getOrInsertGlobal(GlobalName, GlobalType));
    globalVar->setLinkage(GlobalValue::ExternalLinkage);
    if(localThread)
      globalVar->setThreadLocal(true);
    return globalVar;
  }

  /// \brief Helper to find a function with the given name, creating it if it
  /// doesn't already exist. If the function needed to be created then return
  /// false, signifying that the caller needs to add the function body.
  template <typename T>
  bool GetOrCreateFunction(const char *FnName, Module& M,
                           Function *&Fn,
                           Function::LinkageTypes Linkage =
                           Function::InternalLinkage,
                           bool DoesNotThrow = true) {
    LLVMContext &Ctx = M.getContext();
    
    Fn = M.getFunction(FnName);
    if (Fn) {
      return true;
    }
    // Otherwise we have to create it
    FunctionType *FTy = TypeBuilder<T, false>::get(Ctx);
    Fn = Function::Create(FTy, Linkage, FnName, &M);
    // Set nounwind if it does not throw.
    if (DoesNotThrow)
      Fn->setDoesNotThrow();
    return false;
  }

  Function* Get__unwindrts_mysetjmp_callee(Module& M) {
    // Inline assembly to move the callee saved regist to rdi
    Function* Fn = nullptr;
    if (GetOrCreateFunction<mysetjmp_callee_ty>("mysetjmp_callee_llvm", M, Fn))
      return Fn;

    LLVMContext& Ctx = M.getContext();
    BasicBlock* Entry                 = BasicBlock::Create(Ctx, "mysetjmp.entry", Fn);

    Type* Int32Ty = TypeBuilder<int32_t, false>::get(Ctx);
    Value* ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
    Value* ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);

    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;
    using AsmTypeCallee = void (void**);
    FunctionType *FAsmTypeCallee = TypeBuilder<AsmTypeCallee, false>::get(Ctx);

    Value *Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rdi\nmovq %rbp, 0(%rdi)\nmovq %rsp, 16(%rdi)\nmovq %rbx, 24(%rdi)\nmovq %r12, 32(%rdi)\nmovq %r13, 40(%rdi)\nmovq %r14, 48(%rdi)\nmovq %r15, 56(%rdi)\n", "r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    IRBuilder<> B(Entry);

    B.CreateCall(Asm, {argsCtx});
    B.CreateRet(ONE);
    Fn->addFnAttr(Attribute::NoUnwindPath);
    return Fn;
  }

  // Store context of work except for the sp
  Function* Get__unwindrts_mysetjmp_callee_nosp(Module& M) {
    // Inline assembly to move the callee saved regist to rdi
    Function* Fn = nullptr;
    if (GetOrCreateFunction<mysetjmp_callee_ty>("mysetjmp_callee_nosp_llvm", M, Fn))
      return Fn;

    LLVMContext& Ctx = M.getContext();
    BasicBlock* Entry  = BasicBlock::Create(Ctx, "mysetjmp.entry", Fn);

    Type* Int32Ty = TypeBuilder<int32_t, false>::get(Ctx);
    Value* ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
    Value* ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);

    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;
    using AsmTypeCallee = void (void**);
    FunctionType *FAsmTypeCallee = TypeBuilder<AsmTypeCallee, false>::get(Ctx);

    Value *Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rdi\nmovq %rbp, 0(%rdi)\nmovq %rbx, 24(%rdi)\nmovq %r12, 32(%rdi)\nmovq %r13, 40(%rdi)\nmovq %r14, 48(%rdi)\nmovq %r15, 56(%rdi)\n", "r,~{rdi},~{rsi},~{r8},~{r9},~{r10},~{r11},~{rdx},~{rcx},~{rax},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    IRBuilder<> B(Entry);

    B.CreateCall(Asm, {argsCtx});

    //auto OpaqueTrueTy = FunctionType::get(Type::getInt32Ty(Ctx), false);
    //auto OpaqueTrue = InlineAsm::get(OpaqueTrueTy, "xor $0, $0",  "=r,~{dirflag},~{fpsr},~{flags}", false);
    //CallInst* res = B.CreateCall(OpaqueTrue);
    B.CreateRet(ONE);
    Fn->addFnAttr(Attribute::NoUnwindPath);
    return Fn;
  }


  Function* Get__unwindrts_unwind_gnuhash(Module& M) {
    using unwind_gnuhash_ty = unsigned (char *);
    Function* Fn = nullptr;
    if (GetOrCreateFunction<unwind_gnuhash_ty>("unwind_gnuhash_llvm", M, Fn))
      return Fn;
    LLVMContext& C = M.getContext();
    const DataLayout &DL = M.getDataLayout();

    BasicBlock* entry = BasicBlock::Create(C, "entry", Fn);
    BasicBlock* forbodypreheader = BasicBlock::Create(C, "for.body.preheader", Fn);
    BasicBlock* forbody = BasicBlock::Create(C, "for.body", Fn);
    BasicBlock* forend = BasicBlock::Create(C, "for.end", Fn);
    /*
      uint32_t hashGnu(const uint8_t* name) {
      uint32_t h = 5381;
      for (; *name; name++) {
      h = (h << 5) + h + *name;
      }
      return h;
      }
    */
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
    Value* nameLoad = B.CreateAlignedLoad(args, 1, "nameLoad");
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
    auto incdecptr = B.CreateConstGEP1_32(namePhi, 1, "incdecptr");
    auto incdecptrLoad = B.CreateAlignedLoad(incdecptr, 1, "incdecptrLoad");

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

  Function* Get__unwindrts_unwind_queryunwindaddress(Module& M) {
    using unwind_queryunwindaddress_ty = unsigned (long);
    
    //AttributeList AL;
    //AL = AL.addAttribute(C, AttributeList::FunctionIndex,
    //                   Attribute::NoUnwindPath);


    Function* Fn = nullptr;
    if (GetOrCreateFunction<unwind_queryunwindaddress_ty>("unwind_queryunwindaddress_llvm", M, Fn))
      return Fn;

    LLVMContext& C = M.getContext();
    const DataLayout &DL = M.getDataLayout();

    BasicBlock* entry = BasicBlock::Create(C, "entry", Fn);
    BasicBlock* whilebodypreheader = BasicBlock::Create(C, "while.body.preheader", Fn);
    BasicBlock* whilebody = BasicBlock::Create(C, "while.body", Fn);
    BasicBlock* whileendloopexit = BasicBlock::Create(C, "while.end.loopexit", Fn);
    BasicBlock* whileend = BasicBlock::Create(C, "while.end", Fn);

    // Global variable
    GlobalVariable* pbucket = GetGlobalVariable("bucket", TypeBuilder<unsigned*, false>::get(C), M, true);
    GlobalVariable* pnbucket = GetGlobalVariable("nbucket", TypeBuilder<unsigned, false>::get(C), M, true);
    GlobalVariable* pratable = GetGlobalVariable("ratable", TypeBuilder<unsigned*, false>::get(C), M, true);
    GlobalVariable* pchain = GetGlobalVariable("chain", TypeBuilder<unsigned*, false>::get(C), M, true);
    GlobalVariable* punwindtable = GetGlobalVariable("unwindtable", TypeBuilder<unsigned*, false>::get(C), M, true);

    // First argument
    Function::arg_iterator argsIt = Fn->arg_begin();
    Value* args = &*argsIt;

    // Builder
    IRBuilder<> B(entry);

    auto bucket = B.CreateLoad(pbucket);
    auto chain = B.CreateLoad(pchain);
    auto ratable = B.CreateLoad(pratable);
    auto unwindtable = B.CreateLoad(punwindtable);
    auto nbucket = B.CreateLoad(pnbucket);

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
    Constant* gnuhash = UNWINDRTS_FUNC(unwind_gnuhash, M);
    Value* hashVal = B.CreateCall(gnuhash, {loadRAi8}, "hashVal");
#else
    auto args32 = B.CreateTrunc(args, IntegerType::getInt32Ty(C));
    Constant* hashGnui = Get_hashGnui(M);
    Value* hashVal = B.CreateCall(hashGnui, {args32});
#endif

    auto rem = B.CreateURem(hashVal, nbucket, "rem");
    auto idxprom = B.CreateZExt(rem, IntegerType::getInt64Ty(C), "idxprom");

    auto arrayidx = B.CreateInBoundsGEP(bucket, idxprom, "arrayidx");
    auto query016 = B.CreateAlignedLoad(arrayidx, 4, "query.016");
    auto conv = B.CreateTrunc(args,  IntegerType::getInt32Ty(C), "conv");
    auto idxprom117 = B.CreateZExt(query016, IntegerType::getInt64Ty(C), "idxprom117");
    auto arrayidx218 = B.CreateInBoundsGEP(ratable, idxprom117, "arrayidx218");
    auto arrayidx218Load = B.CreateAlignedLoad(arrayidx218, 4, "arrayidx218Load");
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
    auto arrayidx7 = B.CreateInBoundsGEP(chain, idxprom121, "arrayidx7");
    auto query0 = B.CreateAlignedLoad(arrayidx7, 4, "query.0");
    auto idxprom1 = B.CreateZExt(query0, IntegerType::getInt64Ty(C), "idxprom1");
    auto arrayidx2 = B.CreateInBoundsGEP(ratable, idxprom1, "arrayidx2");
    auto arrayidx2load = B.CreateAlignedLoad(arrayidx2, 4, "arrayidx2Load");
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
    auto arrayidx9 = B.CreateInBoundsGEP(unwindtable, idxprom1lcssa, "arrayidx9");
    B.CreateRet(B.CreateAlignedLoad(arrayidx9, 4));

    llvm::InlineFunctionInfo ifi;
    llvm::InlineFunction(dyn_cast<CallInst>(hashVal), ifi, nullptr, true);
    Fn->addFnAttr(Attribute::NoUnwindPath);
    return Fn;
  }


  Function *Get__unwindrts_mylongjmp_callee(Module& M) {
    Function* Fn = nullptr;
    if (GetOrCreateFunction<mylongjmp_callee_ty>("mylongjmp_callee_llvm", M, Fn))
      return Fn;

    LLVMContext& Ctx = M.getContext();
    BasicBlock* Entry           = BasicBlock::Create(Ctx, "mylongjmp.entry", Fn);
    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;
    using AsmTypCallee = void ( void** );
    FunctionType *FAsmTypCallee = TypeBuilder<AsmTypCallee, false>::get(Ctx);
    //Value *Asm = InlineAsm::get(FAsmTypCallee, "movq $0, %rdi\nmovq 0(%rdi), %rbp\nmovq 16(%rdi), %rsp\nmovq 24(%rdi), %rbx\nmovq 32(%rdi), %r12\nmovq 40(%rdi), %r13\nmovq 48(%rdi), %r14\nmovq 56(%rdi), %r15\njmpq *8(%rdi)", "r,~{rdi},~{rbx},~{r12},~{r13},~{r14},~{r15},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    Value *Asm = InlineAsm::get(FAsmTypCallee, "movq $0, %rdi\nmovq 0(%rdi), %rbp\nmovq 16(%rdi), %rsp\nmovq 24(%rdi), %rbx\nmovq 32(%rdi), %r12\nmovq 40(%rdi), %r13\nmovq 48(%rdi), %r14\nmovq 56(%rdi), %r15\njmpq *8(%rdi)", "r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    IRBuilder<> B(Entry);
    B.CreateCall(Asm, argsCtx);
    B.CreateRetVoid();
    Fn->addFnAttr(Attribute::NoUnwindPath);
    return Fn;
  }

  Function *Get__unwindrts_mylongwithoutjmp_callee(Module& M) {
    Function* Fn = nullptr;
    if (GetOrCreateFunction<mylongwithoutjmp_callee_ty>("mylongwithoutjmp_callee_llvm", M, Fn))
      return Fn;

    LLVMContext& Ctx = M.getContext();
    BasicBlock* Entry           = BasicBlock::Create(Ctx, "mywithoutlongjmp.entry", Fn);
    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;
    using AsmTypCallee = void ( void** );
    FunctionType *FAsmTypCallee = TypeBuilder<AsmTypCallee, false>::get(Ctx);
    Value *Asm = InlineAsm::get(FAsmTypCallee, "movq $0, %rdi\nmovq 0(%rdi), %rbp\nmovq 16(%rdi), %rsp\nmovq 24(%rdi), %rbx\nmovq 32(%rdi), %r12\nmovq 40(%rdi), %r13\nmovq 48(%rdi), %r14\nmovq 56(%rdi), %r15\n", "r,~{rdi},~{rbx},~{r12},~{r13},~{r14},~{r15},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);

    IRBuilder<> B(Entry);
    B.CreateCall(Asm, argsCtx);
    B.CreateRetVoid();

    Fn->addFnAttr(Attribute::NoUnwindPath);

    return Fn;
  }

#if 1
  // Create helper function
  Function* GenerateWrapperFunc(CallInst* CI, SmallPtrSet<Value*, 8> storageVec, SmallVector<Instruction *, 4>& insts2clone, Type* workCtxType){
    Function& F = *CI->getCalledFunction();
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();

    const DataLayout &DL = M->getDataLayout();
    auto InternalLinkage = Function::LinkageTypes::InternalLinkage;

    ValueToValueMapTy VMapGotStolenI;

    auto Name = "__prsc_" + F.getName() + "Wrapper";
    auto Fn = M->getFunction(Name.str());
    if (Fn)
      return Fn;

    Type *VoidTy = TypeBuilder<void, false>::get(C);
    FunctionType *FTy = F.getFunctionType();
    assert(!FTy->isFunctionVarArg());
    Type *RetType = FTy->getReturnType();

    Constant* PUSH_WORKCTX = Get_push_workctx(*M);
    Constant* POP_WORKCTX = Get_pop_workctx(*M);

    SmallVector<Type *, 8> WrapperParamTys(FTy->param_begin(), FTy->param_end());
    WrapperParamTys.push_back(workCtxType);
    WrapperParamTys.push_back(IntegerType::getInt8Ty(C)->getPointerTo());

    if(!RetType->isVoidTy()) {
      for(auto storage: storageVec) {
        WrapperParamTys.push_back(storage->getType());
      }
    }
    FunctionType *WrapperFTy = FunctionType::get(VoidTy, WrapperParamTys, /*isVarArg=*/false);

    Function *Wrapper = Function::Create(WrapperFTy, InternalLinkage, Name, M);
    BasicBlock *Entry = BasicBlock::Create(C, "entry", Wrapper);

    unsigned sizeOfOutput = storageVec.size();

    unsigned endIdx = 2; // void** ctx, void* rsp
    if(!RetType->isVoidTy())
      endIdx = endIdx + sizeOfOutput; // void** ctx, void* rsp, storage*

    IRBuilder<> B(Entry);
    SmallVector<Value*, 8> Args;
    for (auto it = Wrapper->arg_begin(); it < Wrapper->arg_end() - endIdx; ++it) {
      Args.push_back(it);
    }

    auto ctxArg = Wrapper->arg_end() - (endIdx);
    auto rspArg = Wrapper->arg_end() - (endIdx-1);
    auto pointerArg= Wrapper->arg_end() - 1;

    // Push the work
    auto res0 = B.CreateCall(PUSH_WORKCTX, {ctxArg, rspArg});
    res0->setTailCall(false);

    CallInst *Result = B.CreateCall(&F, Args);
    Result->setTailCall(false);
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

      // Update the body based on the clone instruction
      for(auto ii: insts2clone) {
        for (Use &U : ii->operands()) {
          Value *v = U.get();
          if(v == CI) {
            SmallVector< Use*, 4 >  useNeed2Update;
            for (auto &use : v->uses()) {
              auto * user = dyn_cast<Instruction>(use.getUser());
              if(user->getParent() == Entry)
                useNeed2Update.push_back(&use);
            }

            for( auto U : useNeed2Update ){
              U->set(Result);
            }

          } else {
            unsigned argLoc = sizeOfOutput+1;
            for(auto Storage : storageVec) {
              argLoc--;
              if(v == Storage) {
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

    auto res1 = B.CreateCall(POP_WORKCTX, {ctxArg, rspArg});
    res1->setTailCall(false);
    B.CreateRetVoid();
    return Wrapper;
  }
#endif

  // Get the actual detach basic block that contains the call
  BasicBlock* traverseDetach(BasicBlock* detachBB, SmallVector<BasicBlock*, 4>& bb2clones) {
    SmallVector<BasicBlock*, 4> bbList;
    ValueMap<BasicBlock*, bool> haveVisited;
    BasicBlock* bb = nullptr;

    BasicBlock* resBB = nullptr;

    bbList.push_back(detachBB);
    bb2clones.push_back(detachBB);
    while(!bbList.empty()) {
      // Visit basic block
      bb = bbList.back();
      bbList.pop_back();

      // If we have not converted it into multiretcall
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
      bb2clones.push_back(bb);

      //auto succBB = detachBB->getUniqueSuccessor();
      //assert(succBB && "Block within detach has multiple successor");

      for ( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {
        auto succBB = *SI;
        bbList.push_back(succBB);
      }

      //bbList.push_back(succBB);
    }

    assert(resBB && "no function call contain in detach");
    return resBB;
  }

  // Get the actual detach basic block that contains the call
  BasicBlock* getActualDetached(BasicBlock* detachBB) {
    SmallVector<BasicBlock*, 4> bbList;
    ValueMap<BasicBlock*, bool> haveVisited;
    BasicBlock* bb = nullptr;

    BasicBlock* resBB = nullptr;

    bbList.push_back(detachBB);
    while(!bbList.empty()) {
      // Visit basic block
      bb = bbList.back();
      bbList.pop_back();

      // If we have not converted it into multiretcall
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

#if 0
      auto succBB = bb->getUniqueSuccessor();
      assert(succBB && "Block within detach has multiple successor");
      bbList.push_back(succBB);
#else
      for ( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {
        auto succBB = *SI;
        bbList.push_back(succBB);
      }
#endif

    }

    assert(resBB && "no function call contain in detach");
    return resBB;
  }

  // Return the set of basic block that is the predecessor of dstBB + dstBB itself
  void getAllPredecessor(BasicBlock* dstBB, SmallPtrSet<BasicBlock*, 8>& allPredBB) {
    SmallVector<BasicBlock*, 4> bbList;
    ValueMap<BasicBlock*, bool> haveVisited;
    BasicBlock* bb = nullptr;

    // Push current dstBB
    allPredBB.insert(dstBB);

    bbList.push_back(dstBB);
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

      for( pred_iterator PI = pred_begin(bb); PI != pred_end(bb); PI++ ) {
        BasicBlock* pred = *PI;
        bbList.push_back(pred);
        // Push predecessor to the allPredBB
        allPredBB.insert(pred);
      }
    }

    return;
  }

  // Handle Potential Jump
  void handlePotentialJump(BasicBlock &BB) {
    auto &C = BB.getParent()->getContext();
    auto BoolTy = Type::getInt1Ty(C);

    for (auto it = BB.begin(); it != BB.end(); ++it) {
      auto &instr = *it;
      auto call = dyn_cast<CallInst>(&instr);
      if (!call) continue;
      auto fn = call->getCalledFunction();
      if (!fn) continue;
      if (fn->getIntrinsicID() != Intrinsic::x86_uli_potential_jump) continue;
      auto afterPotentialJump = it; afterPotentialJump++;

      auto BA = dyn_cast<BlockAddress>(call->getArgOperand(0));
      assert(BA);
      auto InletBlock = BA->getBasicBlock();

      it->eraseFromParent();
      auto afterBB = BB.splitBasicBlock(afterPotentialJump);

      auto terminator = BB.getTerminator();

      auto OpaqueTrueTy = FunctionType::get(BoolTy, false);
      auto OpaqueTrue = InlineAsm::get(OpaqueTrueTy, "xor $0, $0",  "=r,~{dirflag},~{fpsr},~{flags}", false);

      auto cond = CallInst::Create(OpaqueTrue, "", terminator);
      // Somehow need to set this to true to avoid cloberring with the alloca for fork result (analysis restul from MemoryDependency analysis)
      cond->setTailCall(true);
      auto branch = BranchInst::Create(InletBlock, afterBB, cond);

      branch->setMetadata(LLVMContext::MD_prof, MDBuilder(branch->getContext()).createBranchWeights(0, 100));

      ReplaceInstWithInst(terminator, branch);

      // Create a variable annotation indicating that this potential jump, may not be used
      // FIXME: Somehow does not work when BB is entry
      if(BB.getName() != "entry") {
        auto bbIter = &BB;
        BasicBlock* oriBB = nullptr;
        bool bFindBB = false;
        // Look for the basic block that contains the actual call inst that call the function that have stealable continuation
        while ( !bFindBB ) {
          assert(bbIter);
          auto call = dyn_cast<CallInst>(bbIter->getFirstNonPHIOrDbgOrLifetime());
          if (call) {
            auto fn = call->getCalledFunction();
            // Skip basic block if the first inst. is var_annotation or potential jump
            if(fn && (fn->getIntrinsicID() == Intrinsic::var_annotation || fn->getIntrinsicID() == Intrinsic::x86_uli_potential_jump) ) {
              bbIter = bbIter->getUniquePredecessor();
              continue;
            }
          }
          // If the first inst. is the opaque xor
          if(bbIter->getFirstNonPHIOrDbgOrLifetime() == cond) {
            bbIter = bbIter->getUniquePredecessor();
            continue;
          }
          // Find that basic block that contains the call inst.
          bFindBB = true;
          oriBB = bbIter;
        }
        // Create the var annotation
        auto annotateFcn = Intrinsic::getDeclaration(BB.getModule(), Intrinsic::var_annotation);
        IRBuilder<> B (cond);
        auto one = B.getInt32(1); // Indicate that this is a potential jump
        auto stringptr = B.CreateGlobalStringPtr("test", "potentialjump");
        CallInst* res = B.CreateCall(annotateFcn, {BlockAddress::get( oriBB ), stringptr, stringptr, one});
        // Somehow need to set this to true to avoid cloberring with the alloca for fork result (analysis restul from MemoryDependency analysis)
        res->setTailCall(true);
      }
      // -----------------------------------------------------------------------------------------------

      handlePotentialJump(*afterBB);
      return;
    }
    return;
  }

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
  BasicBlock* insertPotentialJump(Instruction *insertPoint, SmallVector<BasicBlock*, 4> &indirectBBs){
    BasicBlock* bb = insertPoint->getParent();
    Function* F = bb->getParent();
    Module* M = F->getParent();
    LLVMContext& C = M->getContext();
    IRBuilder<> B(C);

    auto afterBB = bb->splitBasicBlock(insertPoint->getNextNode());
    auto terminator = bb->getTerminator();
    auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);

    // Create MultiRetCall
    B.SetInsertPoint(bb);
    B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), afterBB, indirectBBs, {});

    // delete the call instruction
    terminator->eraseFromParent();

    return afterBB;
  }

  // Replace Call with MultiRetCall function
  MultiRetCallInst* replaceCallWithMultiRetCall(CallInst *ci, int nIndirectBlock, Function& F) {
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();
    IRBuilder<> B(C);

    auto bb = ci->getParent();
    // Split basic block
    auto afterBB = bb->splitBasicBlock(ci->getNextNode());
    auto terminator = bb->getTerminator();

    SmallVector<BasicBlock *, 4> indirectDests;
    SmallVector<Value *, 4> args;

    unsigned nArgs = ci->getNumArgOperands ();
    for(unsigned i=0; i<nArgs; i++){
      args.push_back(ci->getArgOperand(i));
    }

    std::vector<string> nameBB = {"slowPathEntry", "gotstolenhandlerEntry"};

    for(int i=0; i<nIndirectBlock; i++){
      BasicBlock * bb = BasicBlock::Create(C, nameBB.at(i), &F);
      indirectDests.push_back(bb);
    }

    // Create MultiRetCall
    MultiRetCallInst* mrc = MultiRetCallInst::Create(ci->getCalledFunction(), afterBB, indirectDests, args);
    mrc->setCallingConv(ci->getCallingConv());

    ReplaceInstWithInst(ci, mrc);
    B.SetInsertPoint(afterBB->getFirstNonPHIOrDbgOrLifetime());

    auto newCall = B.CreateRetPad(mrc);

    // delete the call instruction
    terminator->eraseFromParent();

    return mrc;
  }

#if 1
  Function* convertBBtoFcn (Function& F, BasicBlock* detachBB, SmallVector<BasicBlock*, 4>& bb2clones, SmallPtrSet<Value*, 4>& fcnArgs) {

    Module* M = F.getParent();
    LLVMContext& C = M->getContext();

    const DataLayout &DL = M->getDataLayout();
    auto InternalLinkage = Function::LinkageTypes::InternalLinkage;

    ValueToValueMapTy VMapGotStolenI;

    auto Name = "__prsc_" + detachBB->getName() + "_" + F.getName()  + "_wrapper";
    auto Fn = M->getFunction(Name.str());
    if (Fn)
      return Fn;

    Type *VoidTy = TypeBuilder<void, false>::get(C);
    SmallVector<Type *, 8> WrapperParamTys;
    for(auto fcnArg: fcnArgs) {
      WrapperParamTys.push_back(dyn_cast<Value>(fcnArg)->getType());

    }

    FunctionType *WrapperFTy = FunctionType::get(VoidTy, WrapperParamTys, /*isVarArg=*/false);

    Function *Wrapper = Function::Create(WrapperFTy, InternalLinkage, Name, M);
    //BasicBlock *Entry = BasicBlock::Create(C, "entry", Wrapper);

    ValueToValueMapTy VMapSlowPath;
    ValueToValueMapTy VMapSlowPathReverse;


    DebugInfoFinder DIFinder;
    DISubprogram *SP = Wrapper->getSubprogram();
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
      VMapSlowPath[pBB] = CloneBasicBlock(pBB, VMapSlowPath, ".slowPath", Wrapper, nullptr, &DIFinder);
      VMapSlowPathReverse[VMapSlowPath[pBB]] = pBB;
    }

    int argCnt = 0;
    // Iterate through the live variables
    for(auto fcnArg: fcnArgs) {
      Function::arg_iterator args = Wrapper->arg_begin()+argCnt;
      Argument* fcnArgIWrapper =  &*args;

      auto fcnArgI = dyn_cast<Value>(fcnArg);
      SmallVector< Use*, 4 >  useNeed2Update;

      // Get the instruction that uses fcnArgI (fcnArg)
      for (auto &use : fcnArgI->uses()) {
        // user is that instruction
        auto * user = dyn_cast<Instruction>(use.getUser());

        // If user is defined inside the wrapper(the cloned body), then it need to update its operands
        if(user->getParent()->getParent() == Wrapper) {
          useNeed2Update.push_back(&use);
        }
      }
      // Update its operand to use the fcnArgument
      for( auto U : useNeed2Update ){
        U->set(fcnArgIWrapper);
      }

      argCnt++;
    }


    // --------------------------------------------------------------
    for(auto pBB : bb2clones) {
      BasicBlock * ClonedBB = dyn_cast<BasicBlock>(VMapSlowPath[pBB]);

      Instruction * termInst = ClonedBB->getTerminator();
      if(isa<ReattachInst>(termInst) ){
        // Create return
        Instruction* returnInst = ReturnInst::Create(C);
        ReplaceInstWithInst(termInst, returnInst);
      }

      for (Instruction &II : *ClonedBB) {
        // Remap the cloned instruction
        RemapInstruction(&II, VMapSlowPath, RF_IgnoreMissingLocals, nullptr, nullptr);
      }
    }

#if 0
    for(auto pBB : bb2clones) {
      BasicBlock * ClonedBB = dyn_cast<BasicBlock>(VMapSlowPath[pBB]);
      for (Instruction &II : *ClonedBB) {
        //II.dump();
      }
    }
#endif

    return Wrapper;
  }
#endif

#if 1
  void generateWrapperFuncForDetached (Function &F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,
                                       Value* locAlloc, Value* ownerAlloc,
                                       DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>& LVout,
                                       DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
                                       ValueToValueMapTy& VMapSlowPath,
                                       ValueToValueMapTy& VMapGotStolenPath,
                                       SmallPtrSet<BasicBlock*, 8>& GotstolenSet,
                                       DenseMap <DetachInst*, SmallPtrSet<AllocaInst*, 8>>& ReachingAllocSet,
                                       DenseMap <BasicBlock*, SmallPtrSet<AllocaInst*, 8>>& ReachingAllocToGotstolenSet,
                                       DenseMap <DetachInst*, DenseMap <AllocaInst*, StoreInst*>>& LatestStoreForDetach,
                                       DenseMap <BasicBlock*, DenseMap <AllocaInst*, StoreInst*>>& LatestStoreForGotStolen) {
    // Locate the instruct
    Module* M = F.getParent();
    LLVMContext& C = M->getContext();
    IRBuilder<> B(C);

    SmallVector<DetachInst*, 4> bbOrder;
    bbOrder.append(seqOrder.begin(), seqOrder.end());
    bbOrder.append(loopOrder.begin(), loopOrder.end());

    for (auto detachInst: bbOrder) {
      BasicBlock* pBB = detachInst->getParent();
      assert(pBB);
      BasicBlock* detachBBori = detachInst->getDetached();

      auto detachBB = getActualDetached(detachBBori);

      BasicBlock* continueBB  = detachInst->getContinue();
      SmallVector<Instruction *, 4> instsVec;
      for ( auto &II : *detachBB ) {
        instsVec.push_back(&II);
      }

      // Look for the spawn function
      bool bFailToLocateSpawnFunction = true;
      for (auto ii : instsVec) {
        DEBUG(dbgs() << "II: " << *ii << "\n");
        if ((isa<CallInst>(ii) || isa<InvokeInst>(ii)) && isNonPHIOrDbgOrLifetime(ii) ) {
          // Find multiple call inst, need to create wrapper
          if(!bFailToLocateSpawnFunction) {
            bFailToLocateSpawnFunction = true;
            break;
          }
          bFailToLocateSpawnFunction = false;
        }
      }

      // If we fail to locate a spawn instruction, create a function wrapper.
      if(bFailToLocateSpawnFunction) {
        DEBUG(dbgs() << "Need to generate function for inst: " << *detachInst << "\n");

        // Find the basicBlock needed to clone
        SmallVector<BasicBlock*, 4> bb2clones;
        SmallPtrSet<Value*, 4> setBb2clones;
        SmallPtrSet<Value*, 4> fcnArgs;

        BasicBlock* detachBB = detachInst->getDetached();

        // Clone the basic block one at a time
        traverseDetach(detachBB, bb2clones);

        for(auto bb2clone: bb2clones) {
          setBb2clones.insert(bb2clone);
        }

        // LiveInVar determines the function argument
        // Find live instruction into the basic block of the first detach function, create arguments for this live variable
        auto liveOutVars = LVout[detachBB];
        auto liveInVars = LVin[detachBB][detachBB->getUniquePredecessor()];

        DEBUG(dbgs() << "For basic block " << detachBB->getName() << " live variables in: \n");
        // Since in cilk, the return variable is immediately stored in memory, there should be no live variables
        // Look for live variables inside

        for (auto liveInVar : liveInVars) {
          if(liveInVar->getType()->isTokenTy())continue;

          for (auto &use : liveInVar->uses()) {
            auto * user = dyn_cast<Instruction>(use.getUser());
            if(setBb2clones.find(user->getParent()) != setBb2clones.end()) {
              DEBUG(dbgs() << *liveInVar << "\n");
              fcnArgs.insert(liveInVar);
            }
          }
        }

        // Also take into account function arguments
        for(auto it = F.arg_begin(); it != F.arg_end(); it++) {
          for (auto &use : it->uses()) {
            auto * user = dyn_cast<Instruction>(use.getUser());
            if(setBb2clones.find(user->getParent()) != setBb2clones.end()) {
              DEBUG(dbgs() << *it << "\n");
              fcnArgs.insert(it);
            }
          }
        }

        DEBUG(dbgs() << "Basicblock to clone: " << "\n");
        for(auto bb2clone: bb2clones) {
          DEBUG(dbgs() << "BB : " << bb2clone->getName() << "\n");
        }


        // Create the function
        Function* wrapper = convertBBtoFcn(F, detachBB , bb2clones, fcnArgs);
        wrapper->addFnAttr(Attribute::NoInline);
        //wrapper->addFnAttr(Attribute::OptimizeNone);
        //wrapper->addFnAttr("no-frame-pointer-elim");
#if 1
        auto Attrs = wrapper->getAttributes();
        StringRef ValueStr("true" );
        Attrs = Attrs.addAttribute(wrapper->getContext(), AttributeList::FunctionIndex,
                                   "no-frame-pointer-elim", ValueStr);
        wrapper->setAttributes(Attrs);
#endif
        auto bbContainReattach = getActualDetached(detachBB);

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

        B.SetInsertPoint(bbContainReattach->getTerminator());

        SmallVector<Value*, 4> fcnArgVectors(fcnArgs.begin(), fcnArgs.end());

        B.CreateCall(wrapper, fcnArgVectors);

        detachInst->setSuccessor(0, bbContainReattach);

      }

    }
    return ;
  }
#endif

  void instrumentLoop (Function *F, Loop* CurrentLoop, Value* bHaveUnwindAlloc) {
    Module *M = F->getParent();
    LLVMContext& C = M->getContext();
    IRBuilder<> B(M->getContext());

    // Inner most loop, insert ULI polling.
    BasicBlock *HeaderBlock = CurrentLoop->getHeader();
#if 0
    BasicBlock *Latch = CurrentLoop->getLoopLatch();
    outs() << "Loop latch in Clone.cpp\n";
    if(Latch) {
      outs() << "Loop latch name: " << Latch->getName() << "\n";
      if(F->getFnAttribute("poll-at-loop").getValueAsString()=="true") {
	auto splitPt = Latch->getTerminator()->getPrevNode();
        auto afterBB = Latch->splitBasicBlock(splitPt);

        Instruction *term = Latch->getTerminator();
        //B.SetInsertPoint(term);
        B.SetInsertPoint(Latch->getTerminator());

        Value* bHaveUnwind = B.CreateLoad(bHaveUnwindAlloc, 1);
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
      if(F->getFnAttribute("poll-at-loop").getValueAsString()=="true") {
        auto splitPt = HeaderBlock->getFirstNonPHIOrDbgOrLifetime();
        auto afterBB = HeaderBlock->splitBasicBlock(splitPt);

        Instruction *term = HeaderBlock->getTerminator();
        //B.SetInsertPoint(term);
        B.SetInsertPoint(HeaderBlock->getFirstNonPHIOrDbgOrLifetime());

        Value* bHaveUnwind = B.CreateLoad(bHaveUnwindAlloc, 1);
        Value* haveBeenUnwind = B.CreateICmpEQ(bHaveUnwind, B.getInt1(1));

        BasicBlock* loopUnwound = BasicBlock::Create(C, "loop.unwounded", F);

        B.CreateCondBr(haveBeenUnwind, loopUnwound, afterBB);

        term->eraseFromParent();

        B.SetInsertPoint(loopUnwound);

        B.CreateRetVoid();

      }

      B.SetInsertPoint(HeaderBlock->getFirstNonPHIOrDbgOrLifetime());
      Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_unwind_poll);
      B.CreateCall(pollFcn);

      DEBUG(dbgs() << F->getName() << ": Polling at inner most loop\n");
    }


  }

  void insertPollingAtLoop(Loop &L, BasicBlock* unwindPathEntry, Value* bHaveUnwindAlloc) {
    SmallVector<Loop *, 8> VisitStack = {&L};
    Function *F = unwindPathEntry->getParent();

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
        //instrumentLoop(F, CurrentLoop, bHaveUnwindAlloc);
      }
    }
  }

}

namespace llvm {
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
      //AU.addRequired<ReachingDetachInstWrapperPass>();
      //AU.addRequired<ReachingStoreReachableLoadWrapperPass>();    
      //AU.addRequired<LiveVariableWrapperPass>();
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

      return Impl.runImpl(F, AM, DT, DF, LI);
    }

  private:
    LazyDTransPass Impl;


  };
}

// LLVM uses the address of this static member to identify the pass, so the
// initialization value is unimportant.
char LazyDTrans::ID = 0;

#if 0
INITIALIZE_PASS_BEGIN(LazyDTrans, "LazyDTrans",
                      "Lower Tapir to LazyDTrans", false, false)

INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass);
//INITIALIZE_PASS_DEPENDENCY(TargetTransformInfoWrapperPass);
//INITIALIZE_PASS_DEPENDENCY(ReachingDetachInstWrapperPass)
//INITIALIZE_PASS_DEPENDENCY(LiveVariableWrapperPass)
//INITIALIZE_PASS_DEPENDENCY(ReachingStoreReachableLoadWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
//INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
//INITIALIZE_PASS_DEPENDENCY(OptimizationRemarkEmitterWrapperPass)
//INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass);
INITIALIZE_PASS_DEPENDENCY(DominanceFrontierWrapperPass);
//INITIALIZE_PASS_DEPENDENCY(AssumptionCacheTracker);
//INITIALIZE_PASS_DEPENDENCY(MemoryDependenceWrapperPass);


INITIALIZE_PASS_END(LazyDTrans, "LazyDTrans",
                    "Lower Tapir to LazyDTrans", false, false)

#else

INITIALIZE_PASS_BEGIN(LazyDTrans, "LazyDTrans",
                      "Lower Tapir to LazyDTrans", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass);
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominanceFrontierWrapperPass);
INITIALIZE_PASS_END(LazyDTrans, "LazyDTrans",
                    "Lower Tapir to LazyDTrans", false, false)


#endif


// Create the multiretcall from fast path to slow path
void LazyDTransPass::addPotentialJump(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder, ValueToValueMapTy& VMapSlowPath, Value* fromSlowPathAlloc, SSAUpdater& SSAUpdateWorkContext, DenseMap <DetachInst*, SmallPtrSet<AllocaInst*, 8>>& ReachingAllocSet) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
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

    detachBB = getActualDetached(detachBB);

    BasicBlock* continueBB  = detachInst->getContinue();
    SmallVector<Instruction *, 4> instsVec;
    for ( auto &II : *detachBB ) {
      instsVec.push_back(&II);
    }

    // Look for the spawn function
    for (auto ii : instsVec) {
      DEBUG(dbgs() << "II: " << *ii << "\n");
      if ((isa<CallInst>(ii) || isa<InvokeInst>(ii)) && isNonPHIOrDbgOrLifetime(ii) ) {
	// Add a potential jump to slow path
	//B.SetInsertPoint(ii);
	if(EnableMultiRetIR) {

	  BasicBlock * continueSlowPathBB = dyn_cast<BasicBlock>(VMapSlowPath[continueBB]);

	  assert(isa<CallInst>(ii) && "Only supporting call instruction for now");
	  auto mrc = replaceCallWithMultiRetCall(dyn_cast<CallInst>(ii), 2, F);

	  // Perform a branch to continueslowpath bb
	  auto bb1 = mrc->getIndirectDest(0);
	  B.SetInsertPoint(bb1);

#if 0
	  // TODO
	  // Instrumentation here, check if the code is executed by the owner
	  Constant* can_direct_steal = Get_can_direct_steal(*M);
	  B.CreateCall(can_direct_steal);
#endif

#if 0
	  // No need to create retpad in slow path entry since it will mess up the stack provided by thief
	  Function* uliGetWorkCtx = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_get_workcontext);
	  //uliGetWorkCtx->addFnAttr(Attribute::Forkable);
	  auto workCtx = B.CreateCall(uliGetWorkCtx);
	  //workCtx->setTailCall(true);
	  SSAUpdateWorkContext.AddAvailableValue(bb1, workCtx);

	  B.CreateAlignedStore(B.getInt32(1), fromSlowPathAlloc, 4, 1);
#endif

	  auto insertPt = dyn_cast<Instruction>(B.CreateBr(continueSlowPathBB));

	  // Store the reachable alloc in the slow path entry
	  if(!EnableStoreLoadForkStorage) {
	    // Load reachable alloc inst on the top of detach->getParent() and store the result in gotstolen handler
	    for (auto reachingAlloca : ReachingAllocSet[detachInst]){
	      B.SetInsertPoint(detachInst->getParent()->getFirstNonPHIOrDbgOrLifetime());
	      auto * loadRes = B.CreateLoad(reachingAlloca);
	      B.SetInsertPoint(insertPt);
	      insertPt = dyn_cast<Instruction>(B.CreateStore(loadRes, reachingAlloca, true));
	    }
	  }

	} else {
	  B.SetInsertPoint(ii->getNextNode());
	  BasicBlock * continueSlowPathBB = dyn_cast<BasicBlock>(VMapSlowPath[continueBB]);
	  B.CreateCall(potentialJump, {BlockAddress::get( continueSlowPathBB )});

#if 1
	  B.SetInsertPoint(continueSlowPathBB->getFirstNonPHIOrDbgOrLifetime());
	  using AsmTypeCallee = void (void);
	  FunctionType *reloadCaller = TypeBuilder<AsmTypeCallee, false>::get(C);
	  Value *Asm = InlineAsm::get(reloadCaller, "", "~{rdi},~{rsi},~{r8},~{r9},~{r10},~{r11},~{rdx},~{rcx},~{rax},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
	  //???
	  Asm = InlineAsm::get(reloadCaller, "", "~{rbx},~{r12},~{r13},~{r14},~{r15},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);

	  // Create a variable annotation indicating that this either a slow path
	  Function* varAnnotate = Intrinsic::getDeclaration(M, Intrinsic::var_annotation);
	  auto parentSpawn = ii->getParent();
	  auto parentBA = BlockAddress::get( parentSpawn );
	  auto two = B.getInt32(2);
	  auto stringptr = B.CreateGlobalStringPtr("test", "slowpath");
	  CallInst* res = B.CreateCall(varAnnotate, {parentBA, stringptr, stringptr, two});
	  // Somehow need to set this to true to avoid cloberring with the alloca for fork result (analysis restul from MemoryDependency analysis)
	  res->setTailCall(true);
	  // -----------------------------------------------------------------------------------------
#endif
	}

      }
    }
  }
  return;
}


void LazyDTransPass::insertCheckInContBlock(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder, ValueToValueMapTy& VMapSlowPath, Value* fromSlowPathAlloc,
			    DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB, SSAUpdater& SSAUpdateWorkContext) {

  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
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
    B.CreateAlignedStore(B.getInt32(0), fromSlowPathAlloc, 4, 1);

    // Get the slow path continuation
    BasicBlock* continueBBSlowPath  = detachInstSlowPath->getContinue();

    // Split the basic block
    auto insertPt = continueBBSlowPath->getFirstNonPHIOrDbgOrLifetime();
    B.SetInsertPoint(insertPt);

    auto fromSlowPath = B.CreateAlignedLoad(fromSlowPathAlloc, 4, 1);
    auto isFromSlowPath = B.CreateICmpEQ(fromSlowPath, B.getInt32(1), "isFromSlowPath");

    auto splitPt = dyn_cast<Instruction>(isFromSlowPath)->getNextNode();
    auto afterBB = continueBBSlowPath->splitBasicBlock(splitPt);


    BasicBlock* reloadWorkCtxBB = BasicBlock::Create(C, "reloadWorkCtxBB", &F);
    B.SetInsertPoint(reloadWorkCtxBB);

    Function* uliGetWorkCtx = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_get_workcontext);
    //uliGetWorkCtx->addFnAttr(Attribute::Forkable);
    auto workCtx = B.CreateCall(uliGetWorkCtx);
    //workCtx->setTailCall(true);
    B.CreateAlignedStore(B.getInt32(1), fromSlowPathAlloc, 4, 1);
    B.CreateBr(afterBB);

    auto branch = BranchInst::Create(afterBB, reloadWorkCtxBB, isFromSlowPath);
    //auto branch = BranchInst::Create(afterBB);
    ReplaceInstWithInst(continueBBSlowPath->getTerminator(), branch);

    SSAUpdateWorkContext.AddAvailableValue(reloadWorkCtxBB, workCtx);
  }

  return;
}

// Setup the datastructure (map, etc.)
void LazyDTransPass::intializeReconstructSsa(SmallVector<DetachInst*, 4>& bbOrder,
			     DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
			     DenseMap <DetachInst*, SmallPtrSet<Instruction*, 8>>&  RequiredPhiNode,
			     DenseMap<BasicBlock*, SmallPtrSet<Instruction*, 4>>& orig,
			     DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& defsites,
			     DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& PHIsites,
			     SmallPtrSet<Instruction*, 4>& liveInstSet,
			     ValueToValueMapTy& VMapSlowPath,
			     ValueToValueMapTy& VMapSlowPathReverse,
			     DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiUseMap) {
  for (auto detachInst: bbOrder) {
    BasicBlock *pBB = detachInst->getParent();
    assert(pBB);
    BasicBlock* parent = detachInst->getParent();
    BasicBlock* continueBB  = detachInst->getContinue();
    BasicBlock* slowContinueBB = dyn_cast<BasicBlock>(VMapSlowPath[continueBB]);

    auto liveVariableInBB = LVin[continueBB];
    for (auto elem2 : liveVariableInBB) {
      BasicBlock * bbPred = elem2.first;
      // Get live variable in from actual parent
      if (bbPred == parent) {
	for(auto val : elem2.second) {
	  Instruction * liveVar = dyn_cast<Instruction>(val);

	  auto requiredPhiVarSet = RequiredPhiNode[detachInst];
	  if( requiredPhiVarSet.find(liveVar) == requiredPhiVarSet.end() || liveVar->getType()->isTokenTy() ){
	    continue;
	  }

	  Instruction * slowLiveVar = dyn_cast<Instruction>(VMapSlowPath[liveVar]);
	  orig[slowContinueBB].insert(slowLiveVar);
	  defsites[slowLiveVar].insert(slowContinueBB);
	  PHIsites[slowLiveVar].insert(slowContinueBB);

	  defsites[slowLiveVar].insert(slowLiveVar->getParent());

	  PHIsites[slowLiveVar].insert(slowLiveVar->getParent());

	  liveInstSet.insert(slowLiveVar);
	  VMapSlowPathReverse[slowLiveVar] = liveVar;

	  //*****************************
	  // Add existing phi node
	  for (auto &use : slowLiveVar->uses()) {
	    auto * user = dyn_cast<Instruction>(use.getUser());
	    BasicBlock * useBB = user->getParent();
	    if(isa<PHINode>(user)) {
	      PHIsites[slowLiveVar].insert(useBB);
	      phiUseMap[slowLiveVar][useBB] = (dyn_cast<PHINode>(user));
	    }
	  }
	  //*****************************

	}
      }
    }
  }
  return;
}

void LazyDTransPass::insertPhiToReconsructSsa(IRBuilder<>& B,
			      DominanceFrontier& DF,
			      DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
			      DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& defsites,
			      DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& PHIsites,
			      SmallPtrSet<Instruction*, 4>& liveInstSet,
			      ValueToValueMapTy& VMapSlowPathReverse,
			      DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap) {
  for(auto liveInst : liveInstSet) {

    // Push the defsites into a vector
    SmallVector<BasicBlock*, 4> defSitesVector;
    for (auto slowBB : defsites[liveInst]) {
      defSitesVector.push_back(slowBB);
    }

    // Get the def site
    while (!defSitesVector.empty()) {
      auto defBB = defSitesVector.back();
      defSitesVector.pop_back();

      // Get the dominance frontier
      auto DFI = DF.find(defBB);

      if (DFI == DF.end())
	assert(0);
      const std::set<BasicBlock *> &DFs = DFI->second;

      // Iterate the DF
      for (auto slowBB: DFs) {
	// Check if instruction is live
	BasicBlock * fastBB =   dyn_cast<BasicBlock>(VMapSlowPathReverse[slowBB]);
	Instruction * fastLiveVar = dyn_cast<Instruction>(VMapSlowPathReverse[liveInst]);
	auto liveVariableInBB = LVin[fastBB];

	for (auto elem : liveVariableInBB) {
	  auto liveVarSet = elem.second;
	  // If the live variable is still alive
	  bool bCreatePhi = liveVarSet.find(fastLiveVar) != liveVarSet.end();
	  // If a phi node does not exist yet
	  bCreatePhi &= PHIsites[liveInst].find(slowBB) == PHIsites[liveInst].end();
	  // If node is not the definition
	  bCreatePhi &= slowBB != liveInst->getParent();
	  if(bCreatePhi) {
	    // Create a phi node for it
	    B.SetInsertPoint(slowBB->getFirstNonPHI());

	    auto newPhiNode = B.CreatePHI(fastLiveVar->getType(), 2, fastLiveVar->getName() + ".phi");
	    for (auto it = pred_begin(slowBB), et = pred_end(slowBB); it!=et; ++it){
	      BasicBlock* pred = *it;
	      if (isa<DetachInst>(pred->getTerminator())) {
		continue;
	      }
	      newPhiNode->addIncoming(liveInst, pred);
	    }
	    defsites[liveInst].insert(slowBB);

	    PHIsites[liveInst].insert(slowBB);

	    phiMap[liveInst][slowBB] = newPhiNode;
	    defSitesVector.push_back(slowBB);
	  }
	}
      }
    }
  }
  return;
}

void LazyDTransPass::renamePhiNodeToReconstructSsa(DominatorTree &DT,
				   DominanceFrontier& DF,
				   DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>>& PHIsites,
				   SmallPtrSet<Instruction*, 4>& liveInstSet,
				   DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap,
				   DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiUseMap
				   ) {

  SmallVector< Use*, 4 >  useNeed2Update;
  DenseMap <Use*, PHINode*> mapUseToPhi;
  SmallVector< PHINode*, 4 >  phiNeed2Update;
  DenseMap <PHINode*, std::vector<unsigned>> mapPhiToVIncome;
  DenseMap <PHINode*, std::vector<PHINode*>> mapPhiToVPhi;

  for(auto slowLiveVar : liveInstSet) {

    // Find a set of BB that should not be modified
    SmallVector<BasicBlock*, 4> ignoreBBVec;
    SmallPtrSet<BasicBlock*, 4> ignoreBBSet;
    BasicBlock* slowParent = slowLiveVar->getParent();
    // ignoreBBVec : BB dominated by slow parent
    DT.getDescendants(slowParent, ignoreBBVec);

    for(auto ignoreBB : ignoreBBVec) {
      ignoreBBSet.insert(ignoreBB);
    }

    // Find uses that is dominated by the slow path continuation basic block
    for (auto &use : slowLiveVar->uses()) {
      auto * user = dyn_cast<Instruction>(use.getUser());
      BasicBlock * useBB = user->getParent();
      for (auto site : PHIsites[slowLiveVar]) {
	// Get the phi node for this slow live var based on this site
	auto phiN = phiMap[slowLiveVar][site];

	if(!DT.dominates(slowLiveVar, user) && DT.dominates(site, useBB)  && phiN && user != dyn_cast<Instruction>(phiN) )  {
	  if(isa<PHINode>(user)) {
	    // Modify only if the incoming basic block is not from an ignore set
	    // Can be convert into function
	    auto phiInst = dyn_cast<PHINode>(user);
	    unsigned incomingPair = phiInst->getNumIncomingValues();
	    for(unsigned i = 0; i<incomingPair; i++)  {
	      BasicBlock* incomingBB = phiInst->getIncomingBlock(i);
	      Instruction * incomingInst = dyn_cast<Instruction>(phiInst->getIncomingValue(i));
	      if (DT.dominates(site, incomingBB) && incomingInst == slowLiveVar && ignoreBBSet.find(incomingBB) == ignoreBBSet.end() ){
		phiNeed2Update.push_back(phiInst);
		mapPhiToVIncome[phiInst].push_back(i);
		mapPhiToVPhi[phiInst].push_back(phiMap[slowLiveVar][site]);
	      }
	    }
	  } else {
	    // Phi node dominates all uses
	    DEBUG(dbgs() << "Gets modified BB: " << useBB->getName() << " user: " << *user << "\n");
	    useNeed2Update.push_back(&use);
	    mapUseToPhi[&use] = phiN;
	  }
	}
      }
    }

    // Modify phi node entry (located in Dominance Frontier)
    for (auto site : PHIsites[slowLiveVar]) {
      auto DFI = DF.find(site);
      if (DFI == DF.end())
	assert(0);
      const std::set<BasicBlock *> &DFs = DFI->second;
      for (auto dfSite: DFs) {
	if(PHIsites[slowLiveVar].find(dfSite) !=  PHIsites[slowLiveVar].end()){
	  PHINode * phiN = phiMap[slowLiveVar][dfSite];
	  if(!phiN)
	    phiN = phiUseMap[slowLiveVar][dfSite];

	  // If there is no phi node in the DF site?
	  if(!phiN) {
	    continue;
	  }

	  // Find if it uses slowLiveVar, if so replace
	  unsigned incomingPair = phiN->getNumIncomingValues();
	  for(unsigned i = 0; i<incomingPair; i++)  {
	    BasicBlock* incomingBB = phiN->getIncomingBlock(i);
	    Instruction * incomingInst = dyn_cast<Instruction>(phiN->getIncomingValue(i));
	    if (DT.dominates(site, incomingBB) && incomingInst == slowLiveVar && ignoreBBSet.find(incomingBB) == ignoreBBSet.end() ) {

	      phiNeed2Update.push_back(phiN);
	      mapPhiToVIncome[phiN].push_back(i);
	      mapPhiToVPhi[phiN].push_back(phiMap[slowLiveVar][site]);
	    }
	  }
	}
      }
    }
  }


  // Actually modify the use
  for(auto U : useNeed2Update) {
    U->set(mapUseToPhi[U]);
  }
  // Modify the phi node entry
  for(auto P: phiNeed2Update) {
    int i = 0;
    for(auto income: mapPhiToVIncome[P]){
      P->setIncomingValue(income, mapPhiToVPhi[P].at(i));
      i++;
    }
  }

  return;
}

void LazyDTransPass::reconstructSsa(Function& F,
		    ValueToValueMapTy& VMapSlowPathReverse, ValueToValueMapTy& VMapSlowPath,
		    DominatorTree &DT, DominanceFrontier &DF,
		    DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap,
		    DenseMap <DetachInst*, SmallPtrSet<Instruction*, 8>>& RequiredPhiNode,
		    DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
		    SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder) {

  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  DenseMap<BasicBlock*, SmallPtrSet<Instruction*, 4>> orig;
  DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>> defsites;

  // Potential places to replace the slow live var with the phi instrction
  DenseMap<Instruction*, SmallPtrSet<BasicBlock*, 4>> PHIsites;

  DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>> phiUseMap;
  SmallPtrSet<Instruction*, 4> liveInstSet;

  // Initialization
  intializeReconstructSsa(bbOrder, LVin, RequiredPhiNode, orig, defsites, PHIsites, liveInstSet, VMapSlowPath, VMapSlowPathReverse, phiUseMap);

  // Insert phi node in the dominance frontier
  insertPhiToReconsructSsa(B, DF, LVin, defsites, PHIsites, liveInstSet, VMapSlowPathReverse, phiMap);

  // Start renaming basic block dominated by the PhiNodes
  renamePhiNodeToReconstructSsa(DT, DF, PHIsites, liveInstSet, phiMap, phiUseMap);

  return;

}

void LazyDTransPass::insertPhiNodeInSlowPathCont(IRBuilder<> &B, Instruction* liveVar, Instruction* slowLiveVar, BasicBlock* slowContinueBB, BasicBlock * parent,
				 DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap) {
  // Need to create phi node
  if(liveVar->getType()->isTokenTy())
    return;

  // If phiNode is already created in this basic block for the slow variable,
  // Only update the incoming bb and the value associated with it
  int neededUpdate = -1;
  PHINode* piNeededUpdate = nullptr;
  for (auto &use : slowLiveVar->uses()) {
    auto * user = dyn_cast<Instruction>(use.getUser());
    BasicBlock * useBB = user->getParent();
    if(useBB == slowContinueBB && isa<PHINode>(user)) {
      auto piVal = dyn_cast<PHINode> (user);
      unsigned incomingPair = piVal->getNumIncomingValues();
      for(unsigned i = 0; i<incomingPair; i++)  {
	BasicBlock* incomingBB = piVal->getIncomingBlock(i);
	BasicBlock* predPred = incomingBB->getUniquePredecessor();
	if (predPred == parent) {
	  piNeededUpdate = piVal;
	  neededUpdate = i;
	}
      }
    }
  }

  if(neededUpdate>=0 && piNeededUpdate) {
    piNeededUpdate->setIncomingValue(neededUpdate, liveVar);

  } else {
    // Otherwise, create a new phi node
    B.SetInsertPoint(slowContinueBB->getFirstNonPHI());
    auto phiNode = B.CreatePHI(liveVar->getType(), 2, liveVar->getName() + ".phi");
    // Update the incoming value
    for (auto it = pred_begin(slowContinueBB), et = pred_end(slowContinueBB); it!=et; ++it){
      BasicBlock* pred = *it;
      if (isa<DetachInst>(pred->getTerminator())) {
	continue;
      }

      BasicBlock* predPred = pred->getUniquePredecessor();
      bool fromSlowPath = !(predPred == parent);

      if (fromSlowPath) {
	phiNode->addIncoming(slowLiveVar, pred);
      } else {
	phiNode->addIncoming(liveVar, pred);
      }
      phiMap[slowLiveVar][slowContinueBB] = phiNode;
    }
  }

}

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

void LazyDTransPass::updateSSA(SSAUpdater& SSAUpdate, Instruction* inst2replace) {
  SmallVector<Use*, 16> UsesToRename;
  for (Use &U : inst2replace->uses()) {
    Instruction *User = cast<Instruction>(U.getUser());
    if (PHINode *UserPN = dyn_cast<PHINode>(User)) {
      if (UserPN->getIncomingBlock(U) == inst2replace->getParent()) {
	continue;
      }

    } else if (User->getParent() == inst2replace->getParent()) {
      continue;
    }
    UsesToRename.push_back(&U);
  }

  while (!UsesToRename.empty()) {
    SSAUpdate.RewriteUse(*UsesToRename.pop_back_val());
  }
}


// Find the exact clone of the fast inst in the slow path
Instruction* LazyDTransPass::findSlowInst(Instruction *fastInst, Instruction *initialSlowInst, BasicBlock *slowBB) {
  // If slowLiveVar is a phi look for phi located in slowBB
  bool bFoundClone = false;
  ValueMap<Instruction*, bool> haveVisited;

  SmallVector<Instruction*, 4> slowInstList;
  if(isa<PHINode>(initialSlowInst))
    slowInstList.push_back(initialSlowInst);

  Instruction* slowInstFound = initialSlowInst;

  // Visit basic block
  while(!slowInstList.empty()) {
    auto slowInst = slowInstList.back();
    slowInstList.pop_back();

    //auto phiInst = dyn_cast<PHINode>(slowInst);
    if(slowInst->getParent() == slowBB)  {
      bFoundClone=true;
      slowInstFound = slowInst;
      break;
    }

    auto phiInst = dyn_cast<PHINode>(slowInst);
    if(!phiInst) continue;

    if(haveVisited.lookup(slowInst)){
      continue;
    }
    haveVisited[slowInst] = true;

    unsigned incomingPair = phiInst->getNumIncomingValues();
    for(unsigned i = 0; i<incomingPair; i++)  {
      Instruction * incomingInst = dyn_cast<Instruction>(phiInst->getIncomingValue(i));
      if(incomingInst == fastInst)
	continue;
#if 0
      slowInst = incomingInst;
      break;
#else
      slowInstList.push_back(incomingInst);
#endif
    }

    if(bFoundClone)
      break;
  }
  return slowInstFound;
}

// Merge slow path back to fast path
void LazyDTransPass::mergeSlowPathToFastPath(Function& F, SmallVector<SyncInst*, 8>& syncInsts, DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
			     ValueToValueMapTy& VMapSlowPath, DenseMap<BasicBlock*, BasicBlock*>& syncBB2syncPred) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  // Map a sync successor with its predecessor in the slowpath
  DenseMap<Instruction*, Instruction*> fast2slowMap;

  for(auto syncBBi = syncInsts.begin(); syncBBi != syncInsts.end() ; syncBBi++ ) {
    // Merge slow path to fast path
    auto syncInst = *syncBBi;
    auto syncBB = syncInst->getParent();
    auto syncParent = syncInst->getParent();
    auto syncSucc = syncInst->getSuccessor(0);
    auto syncSuccSlow = dyn_cast<BasicBlock>(VMapSlowPath[syncSucc]);
    auto syncInstSlow = dyn_cast<SyncInst>(VMapSlowPath[syncInst]);
    assert(syncInstSlow && "Sync instruction in slow path must exists");

#if 0
    // Jump to sync succ
    if(!syncBB2syncPred.count(syncSucc)) {
      BasicBlock* syncSuccPre = BasicBlock::Create(C, "pre.sync", &F);
      B.SetInsertPoint(syncSuccPre);
      B.CreateBr(syncSucc);
      syncBB2syncPred[syncSucc] = syncSuccPre;

      B.SetInsertPoint(syncSuccPre->getTerminator());
    }

    // Merge the slow path back to fast path
    syncInstSlow->setSuccessor(0, syncBB2syncPred[syncSucc]);
#endif

    // Update the SSA
    auto liveVariableInBB = LVin[syncSucc];
    for (auto elem2 : liveVariableInBB) {
      BasicBlock * bbPred = elem2.first;
      // Get live variable in from actual parent
      if (bbPred == syncBB) {
	for(auto val : elem2.second) {
	  Instruction * liveVar = dyn_cast<Instruction>(val);
	  auto bbLiveVar = liveVar->getParent();

	  // If if live variable is located in the parallel path
	  auto slowLiveVarVal = (VMapSlowPath[liveVar]);
	  if(slowLiveVarVal) {
	    Instruction * slowLiveVar = dyn_cast<Instruction>(slowLiveVarVal);
	    if(!slowLiveVar->hasNUsesOrMore(1))
	      continue;

	    if(liveVar->getType()->isTokenTy())
	      continue;

	    BasicBlock * slowbbLiveVar = dyn_cast<BasicBlock>(VMapSlowPath[bbLiveVar]);
	    assert(slowbbLiveVar && "Can not process this\n");
#if 1

	    Instruction *slowLiveVar2 = findSlowInst(liveVar, slowLiveVar, slowbbLiveVar);
#else
	    // Show be the updated value.
	    Instruction *slowLiveVar2 = slowLiveVar;
#endif
	    fast2slowMap[liveVar] = slowLiveVar2;

	    SSAUpdater SSAUpdate;
	    SSAUpdate.Initialize(liveVar->getType(), liveVar->getName());
	    SSAUpdate.AddAvailableValue(liveVar->getParent(), liveVar);
	    if(slowLiveVar2->getParent() == syncSuccSlow) {
	      SSAUpdate.AddAvailableValue(slowLiveVar2->getParent(), syncBB2syncPred[syncSucc]);
	    }else{
	      SSAUpdate.AddAvailableValue(slowLiveVar2->getParent(), slowLiveVar2);
	    }
	    updateSSA(SSAUpdate, liveVar);
	  }
	}
      }
    }
  }

  // FIXME: rectmul phi node
  // For phi node
  DenseMap<Instruction*, bool> AlreadyAnalyzed;
  for(auto syncBBi = syncInsts.begin(); syncBBi != syncInsts.end() ; syncBBi++ ) {
    // Merge slow path to fast path
    auto syncInst = *syncBBi;
    auto syncBB = syncInst->getParent();
    auto syncParent = syncInst->getParent();
    auto syncSucc = syncInst->getSuccessor(0);
    auto syncSuccSlow = dyn_cast<BasicBlock>(VMapSlowPath[syncSucc]);
    auto syncInstSlow = dyn_cast<SyncInst>(VMapSlowPath[syncInst]);
    assert(syncInstSlow && "Sync instruction in slow path must exists");

    auto liveVariableInBB = LVin[syncSucc];
    for (auto elem2 : liveVariableInBB) {
      BasicBlock * bbPred = elem2.first;
      // Get live variable in from actual parent
      if (bbPred == syncBB) {
	for(auto val : elem2.second) {
	  Instruction * liveVar = dyn_cast<Instruction>(val);
	  auto slowLiveVarVal = (VMapSlowPath[liveVar]);
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

		if(phiInst->getParent() != syncSucc) continue;

		if(AlreadyAnalyzed.count(phiInst)) {
		  continue;
		}

		AlreadyAnalyzed[phiInst]=true;

		// Get all the incoming variable
		unsigned incomingPair = phiInst->getNumIncomingValues();
		for(unsigned i = 0; i<incomingPair; i++)  {
		  BasicBlock* incomingBB = phiInst->getIncomingBlock(i);
		  Instruction* incomingInst = dyn_cast<Instruction>(phiInst->getIncomingValue(i));

		  assert(fast2slowMap[incomingInst] && "Fast inst does not have a slow inst counter part");
		  SSAUpdate.AddAvailableValue(fast2slowMap[incomingInst]->getParent(), fast2slowMap[incomingInst]);

		}
		auto rematerialzeVal = SSAUpdate.GetValueAtEndOfBlock(syncBB2syncPred[syncSucc]);
		phiInst->addIncoming(rematerialzeVal, syncBB2syncPred[syncSucc]);
	      }
	    }
	  }
	}
      }
    }
  }

  return;
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

		for(unsigned i = 0; i<incomingPair; i++)  {
		  BasicBlock* incomingBB = phiInst->getIncomingBlock(i);
		  Instruction* incomingInst = dyn_cast<Instruction>(phiInst->getIncomingValue(i));

		  // If incoming inst is an argument
		  if(!incomingInst) {
		    SSAUpdate.AddAvailableValue(incomingBB, phiInst->getIncomingValue(i));
		    continue;
		  }

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
		auto rematerialzeVal = SSAUpdate.GetValueInMiddleOfBlock(syncBB2syncPred[continueBB]);
		phiInst->addIncoming(rematerialzeVal, syncBB2syncPred[continueBB]);
	      }
	    }
	  }
	}
      }
    }
  }

  // Loop over the sync's parent
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

#if 1
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
#endif

  return;
}

// For instruction in the fast path that always dominate the slow path (does not need a slow path),
// replace the use of the slow path inst version with the one from the fast path
void LazyDTransPass::updateSlowVariables(Function& F,
			 ValueToValueMapTy& VMapSlowPathReverse, ValueToValueMapTy& VMapSlowPath,
			 DominatorTree &DT, DominanceFrontier &DF,
			 DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>>& phiMap,
			 DenseMap <DetachInst*, SmallPtrSet<Instruction*, 8>>& RequiredPhiNode,
			 DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
			 SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder) {

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
	  Instruction * slowLiveVar = dyn_cast<Instruction>(VMapSlowPath[liveVar]);
	  auto requiredPhiVarSet = RequiredPhiNode[detachInst];

	  if(requiredPhiVarSet.find(liveVar) == requiredPhiVarSet.end()){
	    // Replace the instruction in slow path with fast path since it dominates all path
	    replaceUses(liveVar, slowLiveVar);
	  } else {
	    // Insert phi node in slow path continuation
	    insertPhiNodeInSlowPathCont(B, liveVar, slowLiveVar, slowContinueBB, parent, phiMap);
	  }
	}
      } // End if bbPred == parent
    }

  }
  return;
}

#if 0

// Return the phi node that needs to be inserted in the slow path's entry
void LazyDTransPass::findRequiredPhiNodes(DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIPath,
			  DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
			  DenseMap <DetachInst*, SmallPtrSet<Instruction*, 8>>& RequiredPhiNode) {
  for(auto elem: RDIPath) {
    DetachInst * DI = elem.first;
    BasicBlock * parent = DI->getParent();
    BasicBlock * continuation = DI->getContinue();
    // Get the live IN variable
    auto liveVariableInBB = LVin[continuation];
    // Get any basic block from a detach point that can reach this continuation
    auto reachingBB = elem.second;

    for (auto elem2 : liveVariableInBB) {
      BasicBlock * bbPred = elem2.first;
      if (bbPred == parent) {
	for(auto val : elem2.second) {
	  Instruction * liveVar = dyn_cast<Instruction>(val);
	  BasicBlock * livebb = liveVar->getParent();
	  if(reachingBB.find(livebb) != reachingBB.end()){
	    RequiredPhiNode[DI].insert(liveVar);
	  }
	}
      }
    }
  }

#if 0
  // Debugging purpose
  for(auto elem : RequiredPhiNode) {
    DEBUG(dbgs() << "Detach Inst : " << *(elem.first) <<"\n");
    for (auto inst : elem.second) {
      DEBUG(dbgs() << "Required phi " << *inst <<"\n");
    }
    DEBUG(dbgs() << "-------------------\n");
  }
#endif
  return;
}


#else


// If a variable is located in the parallel path, then it needs a phi node
void LazyDTransPass::findRequiredPhiNodes(DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIPath,
			  DenseMap<SyncInst *, SmallPtrSet<BasicBlock*, 8>>& RSIPath,
			  DenseMap<BasicBlock*, BitVector> &MapBB2InVal,
			  DenseMap<BasicBlock *, DenseMap<BasicBlock*, SmallPtrSet<Value*, 8>>>& LVin,
			  SmallVector<SyncInst*, 8>& syncInsts,
			  SmallPtrSet<Instruction*, 8>& RequiredPhiNode) {

  for(auto elem: RDIPath) {
    DetachInst * DI = elem.first;
    BasicBlock * parent = DI->getParent();
    BasicBlock * continuation = DI->getContinue();
    // Get the live IN variable
    auto liveVariableInBB = LVin[continuation];
    // Get any basic block from a detach point that can reach this continuation
    auto reachingBB = elem.second;

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

  for(auto elem: RSIPath) {
    SyncInst * SI = elem.first;
    BasicBlock * parent = SI->getParent();
    auto syncSucc = SI->getSuccessor(0);
    auto liveVariableInBB = LVin[syncSucc];

    // Get any basic block from a detach point that can reach this continuation
    auto reachingBB = elem.second;
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
    DEBUG(dbgs() << "Detach Inst : " << *(elem.first) <<"\n");
    for (auto inst : elem.second) {
      DEBUG(dbgs() << "Required phi " << *inst <<"\n");
    }
    DEBUG(dbgs() << "-------------------\n");
  }
#endif
  return;
}


#endif

void LazyDTransPass::simplifyFcn(Function &F, FunctionAnalysisManager &AM) {
  const SimplifyCFGOptions Options;
#if 0
  auto *TTI = &AM.getResult<TargetIRAnalysis>(F);
  SmallVector<BasicBlock*, 8> bbInF;
  bbInF.clear();
  for( auto &BB : F ) {
    bbInF.push_back(&BB);
  }

  for (auto pBB : bbInF) {
    simplifyCFG(pBB, *TTI, Options);
  }
#endif
  return;
}

void LazyDTransPass::replaceResultOfMultiRetCallWithRetpad(Function &F) {
  for( auto &BB : F ) {
    for (auto &II : BB ) {
      if(isa<MultiRetCallInst>(&II) && !(dyn_cast<MultiRetCallInst>(&II)->getCalledFunction()->getReturnType()->isVoidTy()) ) {
	auto mrc = dyn_cast<MultiRetCallInst>(&II);

	// Get all the retpad
	SmallVector<RetPadInst *, 4> retPadInsts;

	for(auto indirectBB: mrc->getIndirectDests()) {
	  for(auto &ii : *indirectBB) {
	    if(isa<RetPadInst>(&ii)) {
	      retPadInsts.push_back(dyn_cast<RetPadInst>(&ii));
	    }
	  }
	}

	auto bb0 = mrc->getDefaultDest();
	for(auto &ii : *bb0){
	  if(isa<RetPadInst>(&ii)) {
	    retPadInsts.push_back(dyn_cast<RetPadInst>(&ii));
	  }
	}

	SmallVector<Use*, 16> UsesToRename;
	SSAUpdater SSAUpdate;

	SSAUpdate.Initialize(mrc->getType(), mrc->getName());

	for(auto ri: retPadInsts) {
	  SSAUpdate.AddAvailableValue(ri->getParent(), ri);
	}

	// Rename the uses
	for (Use &U : mrc->uses()) {
	  Instruction *User = cast<Instruction>(U.getUser());

	  if (PHINode *UserPN = dyn_cast<PHINode>(User)) {
	    if (UserPN->getIncomingBlock(U) == mrc->getParent()) {
	      continue;
	    }
	  } else if(isa<RetPadInst>(User) || (User->getParent() == mrc->getParent()) ) {
	    continue;
	  }
	  UsesToRename.push_back(&U);
	}

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
      Function *SetupRSPfromRBP = Intrinsic::getDeclaration(F.getParent(), Intrinsic::x86_setup_rsp_from_rbp);
      B.CreateCall(SetupRSPfromRBP);
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
      RemapInstruction(&II, VMapSlowPath, RF_IgnoreMissingLocals, nullptr, nullptr);
    }
  }
  return;
}


void LazyDTransPass::postProcessCfg(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT, SmallPtrSet<AllocaInst*, 8>& AllocaSet,
		    SmallPtrSet<BasicBlock*, 8>& GotstolenSet, DenseMap <BasicBlock*, SmallPtrSet<AllocaInst*, 8>>& ReachingAllocToGotstolenSet,
		    DenseMap <BasicBlock*, DenseMap <AllocaInst*, StoreInst*>>& LatestStoreForGotStolen) {
  // Desirable to  verify the IR before running simplify
  simplifyFcn(F, AM);

  if(!EnableStoreLoadForkStorage) {
    assert(0 && "Pass not available");
#if 0
    // Rerun the analysis (AssumptionCacheTracker does not have a runOnFunction module provided)
    DT.recalculate(F);
    AM.getResult<AAManager>(F);
    AM.getResult<LoopAnalysis>(F);
    AM.getResult<MemoryDependenceAnalysis>(F);
    AM.getResult<OptimizationRemarkEmitterAnalysis>(F);

    // Get the analysis result
    MemoryDependenceResults &MDR = AM.getResult<MemoryDependenceAnalysis>(F);
    AssumptionCache &AC = AM.getResult<AssumptionAnalysis>(F);
    LoopInfo &LI = AM.getResult<LoopAnalysis>(F);

#if 0
    // TODO: Need to be part of lib/Transform/Util folder

    // Run the GVN (the old version) to remove redundant load and create phi instruction
    runOldGVN(false, F, AC, DT,
	      AM.getResult<TargetLibraryAnalysis>(F),
	      AM.getResult<AAManager>(F),
	      &MDR,
	      &LI,
	      &AM.getResult<OptimizationRemarkEmitterAnalysis>(F));
#endif

    // Simplify CFG (in cholesky, these remove redundant phi node created by GVN)
    simplifyFcn(F, AM);

    // Update Dominator Tree
    DT.recalculate(F);
    IRBuilder<> B(F.getContext());

    // Remove store in fast path, too dangerous, don't use.
    SmallVector<StoreInst*, 4 > str2delete;
    for(auto ai : AllocaSet) {
      for (auto &use : ai->uses()) {
	auto * user = dyn_cast<Instruction>(use.getUser());
	if(!use) continue;
	if(isa<StoreInst>(user)  ) {
	  // FIXME: Need to properly remove store, for now keep it.
	  continue;
	  StoreInst * si = dyn_cast<StoreInst>(user);
	  // Remove non volatile store to alloca that stores fork result (volatile implies it is in gotstolen handler or parallel path)
	  if(!si->isVolatile()) {
	    DEBUG(dbgs() << "Remove the non volatile inst :" << *si << "\n");
	    str2delete.push_back(si);
	  }
	} else if (isa<LoadInst>(user)) {
	  LoadInst * li = dyn_cast<LoadInst>(user);
	  li->setVolatile(true);
	}
      }
    }
    // Actually remove store in fast path
    for(auto strInst : str2delete) {
      strInst->eraseFromParent();
    }

    simplifyFcn(F, AM);
#endif
  } else {

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

  }

  // Update the multiretcall inst with the retpad inst
  if(EnableMultiRetIR) {
    replaceResultOfMultiRetCallWithRetpad(F);
  }

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
  Value *Workers = Builder.CreateCall(CILKRTS_FUNC(get_nworkers, *M));
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
  Value *LargeLoopVal = ConstantInt::get(Limit->getType(), 2048);
  Value *Cmp = Builder.CreateICmpULT(LargeLoopVal, SmallLoopVal);
  Value *Grainsize = Builder.CreateSelect(Cmp, LargeLoopVal, SmallLoopVal);



  // Replace uses of grainsize intrinsic call with this grainsize value.
  GrainsizeCall->replaceAllUsesWith(Grainsize);
  return Grainsize;
}

void LazyDTransPass::convertTapirIrToBr(Function &F) {
  DenseMap<Instruction*, Instruction*> replaceInstMap;
  for(auto &BB : F) {
    if(isa<DetachInst>(  BB.getTerminator() )) {
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

  //====================================================================================================
  BasicBlock * unwindPathEntry = BasicBlock::Create(C, "unwind.path.entry", &F);
  B.SetInsertPoint(unwindPathEntry);
  //====================================================================================================
  // Annotate unwind fucntion
  auto annotateFcn = Intrinsic::getDeclaration(M, Intrinsic::var_annotation);
  auto three = B.getInt32(3); // Indicate that this is a unwind handler
  auto stringptr = B.CreateGlobalStringPtr("test", "unwindhandler");
  CallInst* res = B.CreateCall(annotateFcn, {BlockAddress::get( unwindPathEntry ), stringptr, stringptr, three});
  // Somehow need to set this to true to avoid cloberring with the alloca for fork result (analysis restul from MemoryDependency analysis)
  res->setTailCall(true);
  //====================================================================================================
  // Variable needed to pass information between frame
  // TODO: Should be a part of a thread-structure and can be used to pass information between child and parent
  // The amount of stack unwinded: Can be pass through register
  GlobalVariable* gUnwindStackCnt = GetGlobalVariable("unwindStackCnt", TypeBuilder<int, false>::get(C), *M, true);
  // The thread id
  GlobalVariable* gThreadId = GetGlobalVariable("threadId", TypeBuilder<int, false>::get(C), *M, true);
  // Store the original return address (this can be pass through register)
  GlobalVariable* gPrevRa = GetGlobalVariable("prevRa", TypeBuilder<int64_t, false>::get(C), *M, true);
  // Store the original return address (this can be pass through register)
  GlobalVariable* gPrevSp = GetGlobalVariable("prevRa", TypeBuilder<int64_t, false>::get(C), *M, true);
  // Get the work ctx array : Should be global (persist)
  GlobalVariable* gWorkContext = GetGlobalVariable("workctx_arr",
						   workcontext_ty->getPointerTo()->getPointerTo(), *M);

  // Get the context of the program before the unwind: Can be pass through register
  GlobalVariable* gUnwindContext = GetGlobalVariable("unwindCtx", workcontext_ty, *M, true);
  // Save the context in a temporary variable: Can be pass through register
  GlobalVariable* gTmpContext = GetGlobalVariable("tmpCtx", workcontext_ty, *M, true);
  // Get the pointer to the unwind path entry
  GlobalVariable* gSeedSp = GetGlobalVariable("seed_ptr", TypeBuilder<addr_ty*, false>::get(C), *M, true);
  // Get the pointer to the pointer (persist through out unwinding): Should be global (persist)
  GlobalVariable* gBot = GetGlobalVariable("bot", TypeBuilder<int, false>::get(C), *M, true);
  // Get the global variable for the pointer
  GlobalVariable* gUnwindStack = GetGlobalVariable("unwindStack", TypeBuilder<void*, false>::get(C), *M, true);
  //
  //====================================================================================================
  // Function Needed
  Function* getSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);
  Function* getFrameSize = Intrinsic::getDeclaration(M, Intrinsic::x86_get_frame_size);

  // Constant
  Value* ONE = B.getInt32(1);
  Value* ZERO = B.getInt32(0);
  Value* ZERO64 = B.getInt64(0);
  Value* ONEBYTE = ConstantInt::get(IntegerType::getInt64Ty(C), 8, false);
  Value* NULL8 = ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
  Type* Int32Ty = TypeBuilder<int32_t, false>::get(C);

  Constant* MYSETJMP_CALLEE = UNWINDRTS_FUNC(mysetjmp_callee, *M);
  Constant* MYLONGJMP_CALLEE = UNWINDRTS_FUNC(mylongjmp_callee, *M);
  //====================================================================================================
  // Save the context at a temporary variable

  Value* gPTmpContext = B.CreateConstInBoundsGEP2_64(gTmpContext, 0, 0 ); //void**
  if(EnableSaveRestoreCtx) {
    auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);
    auto saveContext = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_save_callee);
    //saveContext->addFnAttr(Attribute::Forkable);
    auto res = B.CreateCall(saveContext, {B.CreateBitCast(gPTmpContext, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});
    res->setTailCall(true);
  } else {
    Value* result = B.CreateCall(MYSETJMP_CALLEE, {gPTmpContext});
    llvm::InlineFunctionInfo ifi;
    llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);
  }

  // TODO: How does this interact with stacklet

  // Get the SP and BP to get my return address
  Value * gThreadIdVal = B.CreateAlignedLoad(gThreadId, 4);
  Value * gUnwindStackCntVal = B.CreateLoad(gUnwindStackCnt);

  // The child original return address
  Value * gPrevRaVal = B.CreateLoad(gPrevRa);

  auto childAddrOfRA = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_child_addressofreturnaddress);
  Value* pChildRA = B.CreateCall(childAddrOfRA);
  pChildRA = B.CreateBitCast(pChildRA, IntegerType::getInt8Ty(C)->getPointerTo()->getPointerTo());

  // Get my return address's address
  auto addrOfRA = Intrinsic::getDeclaration(M, Intrinsic::addressofreturnaddress);
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

    Value* bHaveUnwind = B.CreateLoad(bHaveUnwindAlloc, 1);
    Value* haveBeenUnwind = B.CreateICmpEQ(bHaveUnwind, B.getInt1(1));

    //xchg unwind_stack, rsp
    Value* unwindStack = B.CreateLoad(gUnwindStack);
    Value* mySP = B.CreateCall(getSP);
    B.CreateStore(mySP, gPrevSp);
    using AsmTypeCallee = void (void*);
    FunctionType *FAsmTypeCallee = TypeBuilder<AsmTypeCallee, false>::get(C);
    Value *Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rsp\n", "r,~{rsp},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    B.CreateCall(Asm, {unwindStack});

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

    // If the function has poll-at loop attribute
    if(F.getFnAttribute("poll-at-loop").getValueAsString()=="true") {
      if(EnableUnwindOnce && !DisableUnwindPoll ) {
	B.CreateStore(B.getInt1(1), bHaveUnwindAlloc);
      }
    }

    B.CreateBr(unwindEpilogueBB);
  }
  {
    B.SetInsertPoint(jumpTableBB);

    // Get workctx[threadId]
    // gWorkContext void** * * *
    Value * gWorkContextVal = B.CreateLoad(gWorkContext); //void*[WORKCTX_SIZE] * *
    Value * gWorkContextValPerThread = B.CreateInBoundsGEP(gWorkContextVal, gThreadIdVal); // workctx[threadId] void*[WORKCTX_SIZE] **
    Value * gWorkContextValPerThreadVal = B.CreateLoad(gWorkContextValPerThread); //void*[WORKCTX_SIZE] *

    BasicBlock * nextBlock = jumpTableBB;

    // Create table
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
      auto actualDetachBB = getActualDetached(detachBB);

      if(EnableMultiRetIR)
	B.CreateStore(BlockAddress::get(actualDetachBB, GOTSTOLEN_INDEX), pChildRA);
      else
	B.CreateStore(BlockAddress::get(gotStolenHandler), pChildRA);

      // Update context for particular stack
      // *(&bot)
      Value* botVal = B.CreateLoad(gBot);

      // 1. Move the callee saved register
      // 2. Set the rip
      // 3. The join counter
      // 4. threadId
      // 5. Location of work
      // Use below to convert void[64]* to void**
      //B.CreateConstInBoundsGEP2_64(gTmpContext, 0, 0 ); //void**

      Value* gWorkContextValPerThreadPerBot = B.CreateInBoundsGEP(gWorkContextValPerThreadVal, botVal);
      Value* gWorkContextPtr = B.CreateConstInBoundsGEP2_64(gWorkContextValPerThreadPerBot, 0, 0 ); //void**

      // Savee the callee register
#ifdef OPTIMIZE_UNWIND
      Value* tmpRBP = B.CreateConstGEP1_32(gPTmpContext, I_RBP);
      Value* tmpRSP = B.CreateConstGEP1_32(gPTmpContext, I_RSP);
      Value* tmpR11 = B.CreateConstGEP1_32(gPTmpContext, I_R11);
      Value* tmpRBX = B.CreateConstGEP1_32(gPTmpContext, I_RBX);
      Value* tmpR12 = B.CreateConstGEP1_32(gPTmpContext, I_R12);
      Value* tmpR13 = B.CreateConstGEP1_32(gPTmpContext, I_R13);
      Value* tmpR14 = B.CreateConstGEP1_32(gPTmpContext, I_R14);
      Value* tmpR15 = B.CreateConstGEP1_32(gPTmpContext, I_R15);

      Value* savedRBP = B.CreateConstGEP1_32(gWorkContextPtr, I_RBP);
      Value* savedRSP = B.CreateConstGEP1_32(gWorkContextPtr, I_RSP);
      Value* savedR11 = B.CreateConstGEP1_32(gWorkContextPtr, I_R11);
      Value* savedRBX = B.CreateConstGEP1_32(gWorkContextPtr, I_RBX);
      Value* savedR12 = B.CreateConstGEP1_32(gWorkContextPtr, I_R12);
      Value* savedR13 = B.CreateConstGEP1_32(gWorkContextPtr, I_R13);
      Value* savedR14 = B.CreateConstGEP1_32(gWorkContextPtr, I_R14);
      Value* savedR15 = B.CreateConstGEP1_32(gWorkContextPtr, I_R15);

      B.CreateStore(B.CreateLoad(tmpRBP), savedRBP);
      B.CreateStore(B.CreateLoad(tmpRSP), savedRSP);
      B.CreateStore(B.CreateLoad(tmpR11), savedR11);
      B.CreateStore(B.CreateLoad(tmpRBX), savedRBX);
      B.CreateStore(B.CreateLoad(tmpR12), savedR12);
      B.CreateStore(B.CreateLoad(tmpR13), savedR13);
      B.CreateStore(B.CreateLoad(tmpR14), savedR14);
      B.CreateStore(B.CreateLoad(tmpR15), savedR15);

#ifdef OPTIMIZE_UNWIND_FUNC
      // Call a function to update parallel context (ip, join counter, owner of work, location, locRef
      Value* locAllocAsPointer = B.CreateBitCast(locAlloc, IntegerType::getInt8Ty(C)->getPointerTo());
      Constant* initialize_parallel_ctx = Get_initialize_parallel_ctx(*M);
      B.CreateCall(initialize_parallel_ctx, {gWorkContextPtr, BlockAddress::get(actualDetachBB, STEALENTRY_INDEX), locAllocAsPointer});

#else
      // Store the address of the slow path entry into the temporary context
      Value* savedPc = B.CreateConstGEP1_32(gWorkContextPtr, I_RIP); //void** (no loading involved)

      // workctx[I_RIP] = slow_path_entry;
      if(EnableMultiRetIR)
	B.CreateStore(BlockAddress::get(actualDetachBB, STEALENTRY_INDEX), savedPc);
      else
	B.CreateStore(BlockAddress::get(dyn_cast<BasicBlock>(VMapSlowPath[contBB])), savedPc);

      // Set join counter to 2
      // workctx[joinctr] = (void*) 2;
      Value* twoAsPointer = B.CreateCast(Instruction::IntToPtr, B.getInt32(2), IntegerType::getInt8Ty(C)->getPointerTo());
      Value* joinCtr = B.CreateConstGEP1_32(gWorkContextPtr, I_JOINCNT); //void** (no loading involved)
      B.CreateStore(twoAsPointer, joinCtr);

      // Set the owner of the work
      // workctx[owner] = (void*) threadId;
      Value* threadIdAsPointer = B.CreateCast(Instruction::IntToPtr, gThreadIdVal, IntegerType::getInt8Ty(C)->getPointerTo());
      Value* ownerRef = B.CreateConstGEP1_32(gWorkContextPtr, I_OWNER); //void** (no loading involved)
      B.CreateStore(threadIdAsPointer, ownerRef);

      // Set the location of the work
      // workctx[loc] = (void*) bot;
      Value* botAsPointer = B.CreateCast(Instruction::IntToPtr, botVal, IntegerType::getInt8Ty(C)->getPointerTo());
      Value* locRef = B.CreateConstGEP1_32(gWorkContextPtr, I_LOC); //void** (no loading involved)
      B.CreateStore(botAsPointer, locRef);

      // Set the address of the location
      // workctx[addrloc] = (void*) (&loc);
      Value* locAllocAsPointer = B.CreateBitCast(locAlloc, IntegerType::getInt8Ty(C)->getPointerTo());
      Value* locAllocRef = B.CreateConstGEP1_32(gWorkContextPtr, I_ADDRLOC); //void** (no loading involved)
      B.CreateStore(locAllocAsPointer, locAllocRef);

#endif

      // Store in stack memory
      B.CreateStore(botVal, locAlloc);
      B.CreateStore(gThreadIdVal, ownerAlloc);


#else

      // Store the address of the slow path entry into the temporary context
      Value* savedPc = B.CreateConstGEP1_32(gPTmpContext, I_RIP); //void** (no loading involved)

      if(EnableMultiRetIR)
	B.CreateStore(BlockAddress::get(actualDetachBB, STEALENTRY_INDEX), savedPc);
      else
	B.CreateStore(BlockAddress::get(dyn_cast<BasicBlock>(VMapSlowPath[contBB])), savedPc);

      // Set join counter to 2
      // workctx[joinctr] = (void*) 2;
      Value* twoAsPointer = B.CreateCast(Instruction::IntToPtr, B.getInt32(2), IntegerType::getInt8Ty(C)->getPointerTo());

      Value* joinCtr = B.CreateConstGEP1_32(gPTmpContext, I_JOINCNT); //void** (no loading involved)
      B.CreateStore(twoAsPointer, joinCtr);

      // Set the owner of the work
      // workctx[owner] = (void*) threadId;
      Value* threadIdAsPointer = B.CreateCast(Instruction::IntToPtr, gThreadIdVal, IntegerType::getInt8Ty(C)->getPointerTo());

      Value* ownerRef = B.CreateConstGEP1_32(gPTmpContext, I_OWNER); //void** (no loading involved)
      B.CreateStore(threadIdAsPointer, ownerRef);

      // Set the location of the work
      // workctx[loc] = (void*) bot;
      Value* botAsPointer = B.CreateCast(Instruction::IntToPtr, botVal, IntegerType::getInt8Ty(C)->getPointerTo());
      Value* locRef = B.CreateConstGEP1_32(gPTmpContext, I_LOC); //void** (no loading involved)

      B.CreateStore(botAsPointer, locRef);
      // Store in memory
      B.CreateStore(botVal, locAlloc);

      B.CreateStore(gThreadIdVal, ownerAlloc);

      // Set the address of the location
      // workctx[addrloc] = (void*) (&loc);
      Value* locAllocAsPointer = B.CreateBitCast(locAlloc, IntegerType::getInt8Ty(C)->getPointerTo());

      Value* locAllocRef = B.CreateConstGEP1_32(gPTmpContext, I_ADDRLOC); //void** (no loading involved)

      B.CreateStore(locAllocAsPointer, locAllocRef);

      // TODO: Should remove this, maybe expensive
      // Store work
      // Save the tmpCtx into the workCtx[threadId][bot]
      //Value * gWorkContextValPerThreadPerBot = B.CreateInBoundsGEP(gWorkContextValPerThreadVal, botVal);
      Value* gTmpContextVal = B.CreateLoad(gTmpContext);
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
    Value * gPrevRaToVoid = B.CreateCast(Instruction::IntToPtr, gPrevRaVal, IntegerType::getInt8Ty(C)->getPointerTo());
    B.CreateStore(gPrevRaToVoid, pChildRA);
    //}

    if(F.getFnAttribute("poll-at-loop").getValueAsString()=="true") {
      if(EnableUnwindOnce && !DisableUnwindPoll ) {
	B.CreateStore(B.getInt1(1), bHaveUnwindAlloc);
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
  if(DisablePushPopSeed) {
    // Get the unwind path entry based on return address
    Constant* queryUnwindAddr = UNWINDRTS_FUNC(unwind_queryunwindaddress, *M);
    auto loadRA = B.CreateLoad(myRA); // myRA: int64*, loadRA: int64
    unwindAddrRes = B.CreateCall(queryUnwindAddr, {loadRA});
    unwindEntryVal = B.CreateZExt(unwindAddrRes, IntegerType::getInt64Ty(C));

  } else {
    // Get the unwind entry
    Value* gSeedSpVal = B.CreateLoad(gSeedSp); //void **
    // seed_sp--
    Value* gSeedSpValInt =  B.CreateCast(Instruction::PtrToInt, gSeedSpVal, IntegerType::getInt64Ty(C));
    gSeedSpValInt = B.CreateSub(gSeedSpValInt, ONEBYTE);
    Value* gSeedSpVal2 = B.CreateCast(Instruction::IntToPtr, gSeedSpValInt, IntegerType::getInt8Ty(C)->getPointerTo()->getPointerTo());
    B.CreateStore(gSeedSpVal2, gSeedSp);
    // Get the entry
    unwindEntryVal = B.CreateLoad(gSeedSpVal); //void*
    // Set the value to zero
    B.CreateStore(NULL8, gSeedSpVal);

    unwindEntryVal = B.CreateCast(Instruction::PtrToInt, unwindEntryVal, IntegerType::getInt64Ty(C));

  }
  //====================================================================================================
  // if (*p_parent_unwind == 0)
  Value* isEqZero64 = B.CreateICmpEQ(unwindEntryVal, ZERO64);
  B.CreateCondBr(isEqZero64, resumeInterruptedBB, returnToUnwindBB);

  {
    B.SetInsertPoint(resumeInterruptedBB);

    //B.CreateStore(ZERO, gUnwindStackCnt);
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );

    if(EnableSaveRestoreCtx) {
      auto restoreContext = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_restore_context);
      //restoreContext->addFnAttr(Attribute::Forkable);
      CallInst* result = B.CreateCall(restoreContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(C)->getPointerTo())});
      //result->setTailCall(true);
    } else {
      Value *result = B.CreateCall(MYLONGJMP_CALLEE, {gunwind_ctx});
      dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);

      // FIXME : should be inlined
      llvm::InlineFunctionInfo ifi;
      llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);
    }
    B.CreateUnreachable();
  }
  //====================================================================================================
  {
    B.SetInsertPoint(returnToUnwindBB);

    // TODO: Switch stack
    Value* prevSP = B.CreateLoad(gPrevSp);
    using AsmTypeCallee = void (long);
    FunctionType *FAsmTypeCallee = TypeBuilder<AsmTypeCallee, false>::get(C);
    Value *Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rsp\n", "r,~{rsp},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    B.CreateCall(Asm, {prevSP});

    // Change the gPrevRa to my return address
    B.CreateStore(B.CreateLoad(myRA), gPrevRa);
    // Change my return address to unwnd entry
    B.CreateStore(unwindEntryVal, myRA);

    // Restore rsp to get proper stack
    Function *SetupRSPfromRBP = Intrinsic::getDeclaration(M, Intrinsic::x86_setup_rsp_from_rbp);
    B.CreateCall(SetupRSPfromRBP);

    // return 0; or anything empty
    if(F.getReturnType()->isVoidTy())
      B.CreateRetVoid();
    else if (F.getReturnType()->isIntegerTy())
      B.CreateRet(ConstantInt::get(F.getReturnType(), 0, false));
    else if (F.getReturnType()->isPointerTy())
      B.CreateRet(ConstantPointerNull::get(dyn_cast<PointerType>(F.getReturnType())));
    else if (F.getReturnType()->isFloatingPointTy())
      B.CreateRet(ConstantFP::get(F.getReturnType(), "0"));
    else if (F.getReturnType()->isStructTy()) {
      auto stType = dyn_cast<StructType>(F.getReturnType());
      Value* returnST = B.CreateAlloca(stType, DL.getAllocaAddrSpace(), nullptr, "returnStType");
      Value* returnLoadSt = B.CreateLoad(returnST);
#if 0
      for(auto elem: stType->elements()){
	if(isa<StructType>(elem)) {
	  assert(0 && "Recursive Struct return type not supported yet");
	} else {
	  elem.dump();
	}
      }
#endif
      B.CreateRet(returnLoadSt);
    } else if (F.getReturnType()->isArrayTy()) {
      auto atType = dyn_cast<ArrayType>(F.getReturnType());
      Value* returnAT = B.CreateAlloca(atType, DL.getAllocaAddrSpace(), nullptr, "returnAtType");
      Value* returnLoadAt = B.CreateLoad(returnAT);
      B.CreateRet(returnLoadAt);
    } else if (F.getReturnType()->isVectorTy()) {
      auto vtType = dyn_cast<VectorType>(F.getReturnType());
      Value* returnVT = B.CreateAlloca(vtType, DL.getAllocaAddrSpace(), nullptr, "returnVtType");
      Value* returnLoadVt = B.CreateLoad(returnVT);
      B.CreateRet(returnLoadVt);
    } else {
      errs() << "Have not supported " << *F.getReturnType() << " yet\n";
      assert(0 && "Return type not supported yet");
    }
  }
  //====================================================================================================

  if(DisablePushPopSeed) {
    // Inline the query unwind address from return address
    //llvm::InlineFunctionInfo ifi;
    //llvm::InlineFunction(dyn_cast<CallInst>(unwindAddrRes), ifi, nullptr, true);
  }

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
			    ValueToValueMapTy& VMapGotStolenPath,
			    SmallPtrSet<BasicBlock*, 8>& GotstolenSet,
			    DenseMap <DetachInst*, SmallPtrSet<AllocaInst*, 8>>& ReachingAllocSet,
			    DenseMap <BasicBlock*, SmallPtrSet<AllocaInst*, 8>>& ReachingAllocToGotstolenSet,
			    DenseMap <DetachInst*, DenseMap <AllocaInst*, StoreInst*>>& LatestStoreForDetach,
			    DenseMap <BasicBlock*, DenseMap <AllocaInst*, StoreInst*>>& LatestStoreForGotStolen
			    ) {
  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  for (auto detachInst: bbOrder) {
    BasicBlock* pBB = detachInst->getParent();
    assert(pBB);
    // Get live variable output the detach basic block
    BasicBlock* detachBB = detachInst->getDetached();
    BasicBlock* continueBB = detachInst->getContinue();
    BasicBlock* continueSlowPathBB  = dyn_cast<BasicBlock>(VMapSlowPath[continueBB]);
    auto liveOutVars = LVout[detachBB];
    auto liveInVars = LVin[detachBB][detachBB->getUniquePredecessor()];

#if 0
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
    // For each detach instruction, create a gotstolen handler
    auto gotStolenHandler = createGotStolenHandlerBB(*detachInst, continueBB, locAlloc, ownerAlloc, ReachingAllocSet);
    VMapGotStolenPath[detachBB] = gotStolenHandler;

    // Keep record of the got stolen handler basic block
    GotstolenSet.insert(gotStolenHandler);

    // TODO: Might remove this since no longer needed
#if 0
    // Copy information related to detach-alloca to gotstolen-alloca (contains the same information but use gotstolen basic block as key instead of detach inst, since detach inst will be replaced with branch inst)
    // Create a map from gotstolen handler to a set of reaching alloca
    for (auto reachingAlloca : ReachingAllocSet[detachInst]){
      ReachingAllocToGotstolenSet[gotStolenHandler].insert(reachingAlloca);
    }
    // Transfer information of latest store that reaches detach (basically changing the key from detachinst to gotstolen)
    for (auto reachingAlloca : ReachingAllocSet[detachInst]){
      LatestStoreForGotStolen[gotStolenHandler][reachingAlloca] = LatestStoreForDetach[detachInst][reachingAlloca];
    }
#endif
  }
}

BasicBlock * LazyDTransPass::createGotStolenHandlerBB(DetachInst& Detach, BasicBlock* contBB, Value* locAlloc, Value* ownerAlloc,  DenseMap <DetachInst*, SmallPtrSet<AllocaInst*, 8>>& ReachingAllocSet) {
  BasicBlock* curBB = Detach.getParent();
  Function* F = curBB->getParent();
  Module* M = F->getParent();
  LLVMContext& C = F->getContext();

  Instruction * spawnCI = nullptr;
  Constant* suspend2scheduler = Get_suspend2scheduler(*M);
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);

  BasicBlock * detachBB = Detach.getDetached();

  detachBB = getActualDetached(detachBB);

  BasicBlock * stolenHandlerPathEntry = BasicBlock::Create(C, "gotstolenhandler", F);

  IRBuilder<> builder(C);
  SmallVector<Instruction*, 4> workList;
  Instruction * startOfclone = nullptr;

  // Add potential jump from detachBB to got stolen handler
  // Add potential jump after "spawn to fib" to avoid merging the gotstolen handler and the detachBlock
  for (auto &II: *detachBB) {
    workList.push_back(&II);
  }
  while (!workList.empty()) {
    Instruction &II = *workList.pop_back_val();

    if(EnableMultiRetIR) {
      if(isa<MultiRetCallInst>(&II)) {
	auto mrc = dyn_cast<MultiRetCallInst>(&II);
	// Perform a branch to gotstolen handler bb
	auto bb2 = mrc->getIndirectDest(1);
	builder.SetInsertPoint(bb2);
	builder.CreateRetPad(mrc);
	builder.CreateBr(stolenHandlerPathEntry);

	auto defaultBB = mrc->getDefaultDest();

	startOfclone = defaultBB->getFirstNonPHIOrDbgOrLifetime()->getNextNode();

	spawnCI = mrc;
      }
    } else {
      if ((isa<CallInst>(&II) || isa<InvokeInst>(&II)) && isNonPHIOrDbgOrLifetime(&II) ) {
	// Add a potential jump to gotstolen handler
	CallInst* CI = dyn_cast<CallInst>(&II);
	Function* fcn = CI->getCalledFunction();

	if (fcn->getIntrinsicID() != Intrinsic::x86_uli_potential_jump) {
	  // Get pointer for instruction that needs cloning
	  startOfclone = II.getNextNode()->getNextNode();
	  // Get next node
	  builder.SetInsertPoint(II.getNextNode()->getNextNode());

	  if(EnableMultiRetIR)
	    builder.CreateCall(potentialJump, {BlockAddress::get( detachBB, GOTSTOLEN_INDEX )});
	  else
	    builder.CreateCall(potentialJump, {BlockAddress::get( stolenHandlerPathEntry )});

	  spawnCI = CI;
	}
      }
    }
  }

  assert(startOfclone && "Can not find instruction to clone");

  builder.SetInsertPoint(stolenHandlerPathEntry);
  // Write the content of stolenHandlerEntry
  Value * locVal = builder.CreateLoad(locAlloc, 1, "locVal");
  Value * ownerVal = builder.CreateLoad(ownerAlloc, 1, "ownerVal");
  Instruction * insertInst = builder.CreateCall(suspend2scheduler, {locVal, ownerVal, builder.getInt32(0)});
  dyn_cast<CallInst>(insertInst)->setTailCall(false);

  // Terminate the gotstolen handler
#if 1
  builder.CreateUnreachable();
#else
  if(F->getReturnType()->isVoidTy())
    builder.CreateRetVoid();
  else if (F->getReturnType()->isIntegerTy())
    builder.CreateRet(ConstantInt::get(F->getReturnType(), 0, false));
  else if (F->getReturnType()->isPointerTy())
    builder.CreateRet(ConstantPointerNull::get(dyn_cast<PointerType>(F->getReturnType())));
  else if (F->getReturnType()->isFloatingPointTy())
    builder.CreateRet(ConstantFP::get(F->getReturnType(), "0"));
  else
    assert(0 && "Return type not supported yet");
#endif

  SmallVector<Instruction *, 4> inst2delete;
  SmallVector<Instruction *, 4> insts2clone;

  // Clone instruction after call
  Instruction* ii = startOfclone;
  while(!isa<ReattachInst>(ii)) {
    insts2clone.push_back(ii);
    ii = ii->getNextNode();
  }

  ValueToValueMapTy VMapGotStolenI;
  //Instruction * insertInst = stolenHandlerPathEntry->getFirstNonPHIOrDbgOrLifetime();

  // Clone instruction
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
  Function* varAnnotate = Intrinsic::getDeclaration(M, Intrinsic::var_annotation);
  auto parentSpawn = spawnCI->getParent();
  auto parentBA = BlockAddress::get( parentSpawn );
  auto zero = builder.getInt32(0);
  auto stringptr = builder.CreateGlobalStringPtr("test", "gotstolen");
  CallInst* res = builder.CreateCall(varAnnotate, {parentBA, stringptr, stringptr, zero});
  // Somehow need to set this to true to avoid cloberring with the alloca for fork result (analysis restul from MemoryDependency analysis)
  res->setTailCall(true);
  // Return the stolen handler
  return stolenHandlerPathEntry;
}

void LazyDTransPass::instrumentPushPop(Function& F, SmallVector<BasicBlock*, 8>& bb2clones) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);
  Constant* push_ss  = Get_push_ss(*M);
  Constant* pop_ss = Get_pop_ss(*M);

  if(!DisablePushPopSeed) {
    for (auto pBB : bb2clones){
      Instruction * termInst = pBB->getTerminator();
      if(isa<ReturnInst>(termInst) ){
	B.SetInsertPoint(termInst);
	B.CreateCall(pop_ss);
      }
    }
  }
}

void LazyDTransPass::instrumentSlowPath(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,
			Value* locAlloc, Value* ownerAlloc, Value* bHaveUnwindAlloc, Value* fromSlowPathAlloc, SmallVector<SyncInst*, 8>& syncInsts, ValueToValueMapTy&  VMapSlowPath,
			DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB,
			SSAUpdater& SSAUpdateWorkContext){

  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  // workctx contains information related to running the parallel task, such as join counter callee register, etc.
  // workctx = workctxarr_
  //FunctionType* GetWorkCtxType = TypeBuilder<void** ( void ), false>::get(C);
  //Value* GetWorkCtx = InlineAsm::get(GetWorkCtxType, "movq 8(%rsp), $0\n", "=r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);

  // Loop through the detach basic block that corresponds to the slow path
  for (auto di : bbOrder) {
    auto pBB = di->getParent();
    //outs() << "Processing detach: " << *di << "\n";
    assert(pBB);
    auto diSlowPath = dyn_cast<DetachInst>(VMapSlowPath[di]);
    auto pBBSlowPath = diSlowPath->getParent();
    assert(diSlowPath && "Detach basic block should not have been modified, invariant not met");

    //auto slowPathEntry = dyn_cast<BasicBlock>(VMapSlowPath[di->getContinue()]);
    //assert(slowPathEntry && "slow path entry should not have been modified, invariant not met");

    // Ignore detach that do not have any reaching detaches (since these detaches do not exist in the slow path)
    if(RDIBB[di].empty()) continue;

    // Convert detach into if
    /*
      work_ctx = obtain from rdi
      if(mysetjmp(work_ctx)) {
      increment join ctr atomically
      push_work(ctx);
      run_task()
      decrement join ctr atomically
      pop_work(ctx); // If fail, will suspend to runtime
      }
      // The rest of the work
      continuation:
    */
    auto detachedSlowPath = diSlowPath->getDetached();
    auto continueSlowPath = diSlowPath->getContinue();

    B.SetInsertPoint(diSlowPath);

    auto detachBB = di->getDetached();
    auto actualDetachBB = getActualDetached(detachBB);

    auto multiRetCall = dyn_cast<MultiRetCallInst>(actualDetachBB->getTerminator());
    assert(multiRetCall && "Terminator is not multiretcall inst");

    // Get the workctx
#if 0
    Constant* GetStackletCtxFcnCall = Get_get_stacklet_ctx(*M);
    Value* workCtx = B.CreateCall(GetStackletCtxFcnCall);
#else
    Function* getSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);
    Value* mySP = B.CreateCall(getSP);
    mySP = B.CreateCast(Instruction::IntToPtr, mySP, IntegerType::getInt8Ty(C)->getPointerTo());

    Constant* GetWorkCtxFcnCall = Get_get_workcontext_locowner(*M);
    Value* workCtx = B.CreateCall(GetWorkCtxFcnCall, {B.CreateLoad(locAlloc, 1, "locVal"), B.CreateLoad(ownerAlloc, 1, "ownerVal"), mySP});
#endif

    //workCtx = SSAUpdateWorkContext.GetValueAtEndOfBlock (pBBSlowPath);

    // Function call from library

    //----------------------------------------------------------------------------------------------------
    /*
      Example of changes:

      replace the detach inst with the following:

      %8 = call i8** asm sideeffect "movq %rdi, $0\0A", "=r,~{rdi},~{dirflag},~{fpsr},~{flags}"()
      %9 = call i32 @mysetjmp_callee(i8** %8)
      %10 = icmp eq i32 %9, 0
      br i1 %10, label %det.achd12.slowPath, label %det.cont14.slowPath
    */
    if(EnableSaveRestoreCtx){
      Value* NULL8 = ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
      auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);
      auto saveContextNoSP = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_save_context_nosp);
      //B.CreateCall(saveContextNoSP, {B.CreateBitCast(workCtx, IntegerType::getInt8Ty(C)->getPointerTo()), BlockAddress::get(continueSlowPath)});
      //saveContextNoSP->addFnAttr(Attribute::Forkable);
      auto res = B.CreateCall(saveContextNoSP, {B.CreateBitCast(workCtx, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});
      //res->setTailCall(true);
      //auto insertPoint = B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), detachedSlowPath, {multiRetCall->getIndirectDest(0)}, {});
      auto insertPoint = B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), detachedSlowPath, {continueSlowPath}, {});
      diSlowPath->eraseFromParent();

      //B.SetInsertPoint(insertPoint);
      //B.CreateCall(saveContextNoSP, {B.CreateBitCast(workCtx, IntegerType::getInt8Ty(C)->getPointerTo()), BlockAddress::get(pBBSlowPath, 1)});


    } else {
      Constant* MYSETJMP_CALLEE_NOSP = UNWINDRTS_FUNC(mysetjmp_callee_nosp, *M);
      auto setjmp = B.CreateCall(MYSETJMP_CALLEE_NOSP, {(workCtx)});

      if(EnableMultiRetIR) {
	auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);
	//B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), detachedSlowPath, {multiRetCall->getIndirectDest(0)}, {});
	B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), detachedSlowPath, {continueSlowPath}, {});
	diSlowPath->eraseFromParent();
      } else {
	auto isEqZero64 = B.CreateICmpEQ(setjmp, B.getInt32(0));
	auto branchInst = BranchInst::Create(detachedSlowPath, continueSlowPath, isEqZero64);
	ReplaceInstWithInst(diSlowPath, branchInst);
      }
    }

    // Replace reattach with branch (if detach is removed, reattach should also remove, otherwise invariant assume in passes is not met
    auto actualDetachedSlowPath = getActualDetached(detachedSlowPath);
    ReattachInst* reattachInst = dyn_cast<ReattachInst>(actualDetachedSlowPath->getTerminator());
    BasicBlock* contBB = reattachInst->getDetachContinue();
    BranchInst* brInst = BranchInst::Create(contBB);
    ReplaceInstWithInst(reattachInst, brInst);


    //----------------------------------------------------------------------------------------------------
    // Modify the prologue and epilogue of detached Block
    /*
      Example of changes:

      // Add the push work context (also increment join counter in this function)
      call void @push_workctx(i8** %8)

      %sub11.slowPath = add nsw i32 %n, -3
      %call13.slowPath = tail call i32 @fib(i32 %sub11.slowPath)
      store volatile i32 %call13.slowPath, i32* %a, align 4

      // Add the pop work context (also decrement join counter in this function and synchronize)
      call void @push_workctx(i8** %8)

      %11 = call i8** @pop_workctx()
      reattach within %syncreg, label %det.cont14.slowPath
    */
    Constant* PUSH_WORKCTX = Get_push_workctx(*M);
    Constant* POP_WORKCTX = Get_pop_workctx(*M);
    B.SetInsertPoint(detachedSlowPath->getFirstNonPHIOrDbgOrLifetime());

    if(EnableSaveRestoreCtx) {
      Value* savedPc = B.CreateConstGEP1_32(workCtx, 1);
      B.CreateStore(BlockAddress::get(pBBSlowPath, 1), savedPc);
    }

#if 0

    B.CreateCall(PUSH_WORKCTX, {(workCtx)});

    B.SetInsertPoint(detachedSlowPath->getTerminator());
    workCtx = B.CreateCall(GetStackletCtxFcnCall);

    B.CreateCall(POP_WORKCTX, {workCtx});

#else
    bool bStartClone = false;
    SmallVector<Instruction *, 4> insts2clone;
    SmallPtrSet<Instruction *, 4> insts2cloneSet;


    CallInst* ci = nullptr;
    //StoreInst* si = nullptr;
    SmallPtrSet<Value*, 8> storageVec;
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
	if(ci->getCalledFunction()->getReturnType()->isVoidTy()) {
	  break;
	}
      }
    }

    assert(ci && "No call inst found in slowpath");

    // Find variables used by clone function but defined outside
    for(auto ii : insts2clone) {
      for (Use &U : ii->operands()) {
	Value *v = U.get();
	if(v && isa<Instruction>(v) ) {
	  auto instV = dyn_cast<Instruction>(v);
	  if(insts2cloneSet.find(instV) == insts2cloneSet.end() && instV  != ci)
	    storageVec.insert(v);
	} else if (v && isa<Argument>(v)) {
	  storageVec.insert(v);
	}
      }
    }

    B.SetInsertPoint(detachedSlowPath->getTerminator());

#if 0
    workCtx = B.CreateCall(GetStackletCtxFcnCall);
#else
    mySP = B.CreateCall(getSP);
    mySP = B.CreateCast(Instruction::IntToPtr, mySP, IntegerType::getInt8Ty(C)->getPointerTo());
    workCtx = B.CreateCall(GetWorkCtxFcnCall, {B.CreateLoad(locAlloc, 1, "locVal"), B.CreateLoad(ownerAlloc, 1, "ownerVal"), mySP});
#endif
    Function* wrapperFcn = nullptr;
    if(!ci->getCalledFunction()->getReturnType()->isVoidTy())
      wrapperFcn = GenerateWrapperFunc(ci, storageVec, insts2clone, workCtx->getType());
    else
      wrapperFcn = GenerateWrapperFunc(ci, storageVec, insts2clone, workCtx->getType());

    wrapperFcn->addFnAttr(Attribute::NoUnwindPath);
    wrapperFcn->addFnAttr(Attribute::NoInline);
    wrapperFcn->addFnAttr(Attribute::OptimizeNone); // Can cause a ud2 in assembly?

#if 1
    auto Attrs = wrapperFcn->getAttributes();
    StringRef ValueStr("true" );
    Attrs = Attrs.addAttribute(wrapperFcn->getContext(), AttributeList::FunctionIndex,
			       "no-frame-pointer-elim", ValueStr);
    wrapperFcn->setAttributes(Attrs);
#endif


    SmallVector<Value*, 4> args;
    for(int i = 0; i<ci->getNumArgOperands(); i++){
      args.push_back(ci->getArgOperand(i));
    }
    args.push_back(workCtx);

    //Function* getSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);
    //Value* mySP = B.CreateCall(getSP);
    //mySP = B.CreateCast(Instruction::IntToPtr, mySP, IntegerType::getInt8Ty(C)->getPointerTo());

    args.push_back(mySP);

    if(!ci->getCalledFunction()->getReturnType()->isVoidTy()) {
      for(auto storage : storageVec) {
	args.push_back(storage);
      }
    }
    B.CreateCall(wrapperFcn, {args});

    while(!insts2clone.empty()) {
      auto ii = insts2clone.back();
      insts2clone.pop_back();
      ii->eraseFromParent();
    }
    ci->eraseFromParent();
#endif

#if 0
    B.CreateAlignedStore(B.getInt32(1), fromSlowPathAlloc, 4, 1);
#endif

    //----------------------------------------------------------------------------------------------------
    /*
      Example of changes:

      det.cont14.slowPath:                              ; preds = %if.end10.slowPath, %det.achd12, %det.achd12.slowPath
      %call2.phi = phi i32 [ %call2, %det.achd12 ], [ %call2.slowPath, %det.achd12.slowPath ]

      is converted to:

      det.cont14.slowPath:                              ; preds = %if.end10.slowPath, %det.achd12, %det.achd12.slowPath
      %call2.phi = phi i32 [ %call2, %det.achd12 ], [ %call2.slowPath, %det.achd12.slowPath ], [ %call2.slowPath, %if.end10.slowPath ]

      Basically in the slow path, the detach is converted into a branch, hence in the continuation of the detach, the phi node that exists there should
      also capture the dataflow from the detach's parent
    */
    if(!EnableSSAUpdateTransformation) {
      for (auto& ii : *continueSlowPath) {
	if(isa<PHINode>(&ii)) {
	  PHINode* phiN = dyn_cast<PHINode>(&ii);
	  errs() << "Phi inst: " << *phiN << "\n";
	  unsigned incomingPair = phiN->getNumIncomingValues();
	  Value * inst2copy = nullptr;
	  for(unsigned i = 0; i<incomingPair; i++)  {
	    BasicBlock* incomingBB = phiN->getIncomingBlock(i);
	    if ( incomingBB == detachedSlowPath ) {
	      inst2copy = (phiN->getIncomingValue(i));
	    }
	  }
	  if(inst2copy) {
	    errs() << "Add incoming : " << *inst2copy << "at bb : " << pBBSlowPath->getName() << "\n";
	    phiN->addIncoming(inst2copy, pBBSlowPath);
	  }
	}
      }
    }

#if 0
    // Look for phi node in contBBSlowPat, and remove any incoming value from BB(parent of detach inst)
    for(auto &ii: *continueSlowPath) {
      if(isa<PHINode>(&ii)){
	// Removie incoming value from continue
	SmallVector<BasicBlock*, 4> removeBBs;
	PHINode* phiN = dyn_cast<PHINode>(&ii);
	unsigned incomingPair = phiN->getNumIncomingValues();
	for(unsigned i = 0; i<incomingPair; i++)  {
	  BasicBlock* incomingBB = phiN->getIncomingBlock(i);
	  if ( incomingBB == pBBSlowPath ) {
	    removeBBs.push_back(pBBSlowPath);
	  }
	}
	for(auto bb: removeBBs) {
	  phiN->removeIncomingValue(bb);
	}
      }
    }
#endif

  }


#if 1
  Value* NULL8 = ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
  // Get the sync instruction that corresponds to the slow path
  for(auto syncInst : syncInsts) {
    auto syncBB = syncInst->getParent();
    auto syncSlowPath = dyn_cast<SyncInst>(VMapSlowPath[syncInst]);
    auto syncBBSlowPath = syncSlowPath->getParent();

    //auto syncBBSlowPath = dyn_cast<BasicBlock>(VMapSlowPath[syncBB]);
    assert(syncSlowPath && "Sync inst should not have been modified, invariant not met");
    assert(syncBBSlowPath && "Sync basic block should not have been modified, invariant not met");

    BasicBlock* syncSaveCtxBB = BasicBlock::Create(C, "sync.savectx", &F);
    BasicBlock* syncRuntimeBB = BasicBlock::Create(C, "sync.resume.to.scheduler", &F);

    //auto syncSlowPath = syncBBSlowPath->getTerminator();
    BasicBlock* syncSucc = syncSlowPath->getSuccessor(0);

    // Get the work ctx (again)
    B.SetInsertPoint(syncSlowPath);

    //B.SetInsertPoint(syncSlowPath);

    // Check if we can resume directly
    Function* getSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);
    Value* mySP = B.CreateCall(getSP);
    mySP = B.CreateCast(Instruction::IntToPtr, mySP, IntegerType::getInt8Ty(C)->getPointerTo());

    Value * locVal = B.CreateLoad(locAlloc, 1, "locVal");
    Value * ownerVal = B.CreateLoad(ownerAlloc, 1, "ownerVal");

    // FIXME: Why is not working for cholesky
    //if(EnableUnwindOnce && !DisableUnwindPoll) {
    //B.CreateStore(B.getInt1(0), bHaveUnwindAlloc);
    //}

    Constant* sync_slowpath = Get_sync_slowpath(*M);
    auto canResume = B.CreateCall(sync_slowpath, {locVal, ownerVal, mySP});
    auto canResume2 = B.CreateICmpEQ(canResume, B.getInt8(1));
    B.CreateCondBr(canResume2, syncSucc, syncSaveCtxBB);

    B.SetInsertPoint(syncSaveCtxBB);

    //Value* workCtx = B.CreateCall(GetWorkCtx);
    Constant* GetWorkCtxFcnCall = Get_get_workcontext(*M);
    // Get the workctx
    Constant* GetStackletCtxFcnCall = Get_get_stacklet_ctx(*M);
    Value* workCtx = B.CreateCall(GetStackletCtxFcnCall);

    //workCtx = SSAUpdateWorkContext.GetValueAtEndOfBlock (syncBBSlowPath);
    Value* workCtx2 = B.CreateCall(GetWorkCtxFcnCall, {workCtx});

    /*
      %15 = call i8** asm sideeffect "movq %rdi, $0\0A", "=r,~{rdi},~{dirflag},~{fpsr},~{flags}"()
      %16 = call i32 @mysetjmp_callee(i8** %15)
      %17 = icmp eq i32 %16, 0
      br i1 %17, label %sync.resume.to.scheduler2, label %sync.continue17.slowPath
    */

    CallInst* setjmp = nullptr;

    if(EnableSaveRestoreCtx) {
      auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);
      auto saveContextNoSP = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_save_context_nosp);
      //saveContextNoSP->addFnAttr(Attribute::Forkable);
      CallInst* result = B.CreateCall(saveContextNoSP, {B.CreateBitCast(workCtx2, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});
      //result->setTailCall(true);
      B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), syncRuntimeBB, {syncSucc}, {});
      syncSlowPath->eraseFromParent();

#if 0
      // Modify the phi node in syncSucc
      for(auto &ii: *syncSucc) {
	if(isa<PHINode>(&ii)){
	  // Change the incoming BB from syncSlowPath to syncBB2syncPred[syncSucc]
	  PHINode* phiN = dyn_cast<PHINode>(&ii);
	  unsigned incomingPair = phiN->getNumIncomingValues();
	  for(unsigned i = 0; i<incomingPair; i++)  {
	    BasicBlock* incomingBB = phiN->getIncomingBlock(i);
	    if ( incomingBB == syncBBSlowPath ) {
	      phiN->setIncomingBlock(i, syncBB2syncPred[syncSucc]);
	    }
	  }
	}
      }
#endif

    } else {
      B.SetInsertPoint(syncSlowPath);

      Constant* MYSETJMP_CALLEE_NOSP = UNWINDRTS_FUNC(mysetjmp_callee_nosp, *M);
      setjmp = B.CreateCall(MYSETJMP_CALLEE_NOSP, {(workCtx2)});

      if(EnableMultiRetIR) {
	auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);
	B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), syncRuntimeBB, {syncSucc}, {});
	syncSlowPath->eraseFromParent();
      } else {
	auto isEqZero64 = B.CreateICmpEQ(setjmp, B.getInt32(0));
	auto branchInst = BranchInst::Create(syncRuntimeBB, syncSucc, isEqZero64);
	ReplaceInstWithInst(syncSlowPath, branchInst);
      }

    }

    /*
      sync.resume.to.scheduler:                         ; preds = %det.cont.slowPath
      call void @resume2scheduler(i8** %8)
      br label %sync.continue.slowPath
    */

    // Create a basic block that performs the synchronization
    B.SetInsertPoint(syncRuntimeBB);
    Value* savedPc = B.CreateConstGEP1_32(workCtx2, 1); //void** (no loading involved)

    if(EnableMultiRetIR)
      B.CreateStore(BlockAddress::get(syncSaveCtxBB, 1), savedPc);
    else
      B.CreateStore(BlockAddress::get(syncSucc), savedPc);

    Value* newsp = B.CreateConstGEP1_32(workCtx, 18);
    newsp = B.CreateLoad(newsp);

    // FIXME: Why is not working for cholesky
    //if(EnableUnwindOnce && !DisableUnwindPoll) {
    //B.CreateStore(B.getInt1(0), bHaveUnwindAlloc);
    //}

    Constant* resume2scheduler = Get_resume2scheduler(*M);
    B.CreateCall(resume2scheduler, {workCtx2, newsp});
    B.CreateUnreachable();
    //B.CreateBr(syncSucc);

    // Inline the setjmp
    if(setjmp) {
      llvm::InlineFunctionInfo ifi;
      llvm::InlineFunction(dyn_cast<CallInst>(setjmp), ifi, nullptr, true);
    }
#if 1
    /*
      in rectmul.cpp

      %b.0.slowPath = phi i32 [ %call7.slowPath, %det.cont.slowPath ], [ %call16.slowPath, %det.cont11.slowPath ]

      to

      %b.0.slowPath = phi i32 [ %call7.slowPath, %det.cont.slowPath ], [ %call16.slowPath, %det.cont11.slowPath ], [ %call7.slowPath, %sync.resume.to.scheduler ], [ %call16.slowPath, %sync.resume.to.scheduler2 ]

    */

    // Fix Phi node since using direct resume, the pre.Sync will have at least two predecessor
    for (auto& ii : *syncSucc) {
      if(isa<PHINode>(&ii)) {
	PHINode* phiN = dyn_cast<PHINode>(&ii);
	unsigned incomingPair = phiN->getNumIncomingValues();
	Value * inst2copy = nullptr;
	for(unsigned i = 0; i<incomingPair; i++)  {
	  BasicBlock* incomingBB = phiN->getIncomingBlock(i);
	  if ( incomingBB == syncBBSlowPath ) {
	    inst2copy = (phiN->getIncomingValue(i));
	  }
	}
	if(inst2copy) {
	  phiN->addIncoming(inst2copy, syncSaveCtxBB);
	}
      }
    }
#endif

  }
#endif

  return;
}

void LazyDTransPass::instrumentMainFcn(Function& F) {
  // Initialize the PRSC at the beginning of main
  Module* M = F.getParent();
  IRBuilder<> B(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

  Constant* INITWORKERS_ENV = Get_initworkers_env(*M);
  Constant* DEINITWORKERS_ENV = Get_deinitworkers_env(*M);
  Constant* INITPERWORKERS_SYNC = Get_initperworkers_sync(*M);
  Constant* DEINITPERWORKERS_SYNC = Get_deinitperworkers_sync(*M);

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
  auto * fcn = UNWINDRTS_FUNC(mylongwithoutjmp_callee, M);
  fcn->addFnAttr(Attribute::NoUnwindPath);
  fcn = UNWINDRTS_FUNC(mylongjmp_callee, M);
  fcn->addFnAttr(Attribute::NoUnwindPath);
  fcn = UNWINDRTS_FUNC(mysetjmp_callee, M);
  fcn->addFnAttr(Attribute::NoUnwindPath);
  fcn = UNWINDRTS_FUNC(mysetjmp_callee_nosp, M);
  fcn->addFnAttr(Attribute::NoUnwindPath);
  fcn = UNWINDRTS_FUNC(unwind_gnuhash, M);
  fcn->addFnAttr(Attribute::NoUnwindPath);
  fcn = UNWINDRTS_FUNC(unwind_queryunwindaddress, M);
  fcn->addFnAttr(Attribute::NoUnwindPath);
  
#ifdef OPTIMIZE_UNWIND
  fcn->addFnAttr(Attribute::NoInline);
#endif

  if(fcn)
    return true;

  return false;
}


// We don't modify the program, so we preserve all analyses
void LazyDTransPass::runAnalysisUsage(AnalysisUsage &AU) const  {
  AU.addRequired<LoopInfoWrapperPass>();
  //AU.addRequired<TargetTransformInfoWrapperPass>();
  //AU.addRequired<LiveVariableWrapperPass>();
  //AU.addRequired<ReachingDetachInstWrapperPass>();
  //AU.addRequired<ReachingStoreReachableLoadWrapperPass>();
  AU.addRequired<DominatorTreeWrapperPass>();
  //AU.addRequired<TargetLibraryInfoWrapperPass>();
  //AU.addRequired<OptimizationRemarkEmitterWrapperPass>();
  //AU.addRequired<AAResultsWrapperPass>();
  AU.addRequired<DominanceFrontierWrapperPass>();
  //AU.addRequired<AssumptionCacheTracker>();
  //AU.addRequired<MemoryDependenceWrapperPass>();
}


bool LazyDTransPass::runImpl(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT,  DominanceFrontier &DF, LoopInfo &LI)  {
  if(F.getName() == "main") {
    outs() << "Source filename: " << F.getParent()->getSourceFileName() << "\n";
    if(EnableMainInstrumentation)
      instrumentMainFcn(F);
    //F.addFnAttr(Attribute::NoUnwindPath);
    F.addFnAttr(Attribute::ULINoPolling);
    for(auto &BB : F) {
      for(auto &II : BB) {
	if (isa<DetachInst>(&II)) {
	  errs() << "Warning,detach inside main\n";
	}
      }
    }
  }

  // Why?
  // qsort will generate an error without this
  if(F.getName().contains(F.getParent()->getSourceFileName())) {
    //errs() << "qsort will generate error here\n";
    F.addFnAttr(Attribute::NoUnwindPath);
  }

  // Do not process function that have the nounwindpath attribute
  if(F.hasFnAttribute(Attribute::NoUnwindPath)) {
    return false;
  }

  LiveVariable LV;
  ReachingDetachInst RDI;
  ReachingStoreReachableLoad RSI;

  LV.recalculate(F);
  RDI.recalculate(F, AM, DT, LI);
  RSI.recalculate(F, AM, DT, LI);

  auto  &LVin = LV.getLiveInInstBBMap();
  auto  &LVout = LV.getLiveOutInstBBMap();

  auto  &RDIPath = RDI.getReachingDetachPathMap();
  auto  &RSIPath = RDI.getReachingSyncPathMap();
  auto  &MapBB2InVal = RDI.getMapBB2InVal();

  auto  &RDIBB = RDI.getReachingDetachBBMap();

  auto  &RSBB = RSI.getReachingStore();

  // Get order of update. SeqOrder and looporder contains the Detach's Parent (detach's basic block)
  auto  &seqOrder = RDI.getSeqOrderInst();
  auto  &loopOrder = RDI.getLoopOrderInst();


  // The phi node needed in the continuation in slow path (Key: Detach inst. Value: Live variables defined in between detach inst).
  //DenseMap <DetachInst*, SmallPtrSet<Instruction*, 8>> RequiredPhiNode;
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
  // Store all the gotstolen handler
  SmallPtrSet<BasicBlock*, 8> GotstolenSet;
  // Store all the multiretcall that can be transformed into branch based on path
  SmallPtrSet<MultiRetCallInst*, 8> MultiRetCallPathSet;


  // Similar to ReachingAllocSet but for gotstolen handler
  // TODO: May need to remove both of this since no longer needed
  DenseMap <BasicBlock*, SmallPtrSet<AllocaInst*, 8>> ReachingAllocToGotstolenSet;
  DenseMap <BasicBlock*, DenseMap <AllocaInst*, StoreInst*>> LatestStoreForGotStolen;

  // Key detachInst (or its gotstolen handler) + any alloca inst reaching to it
  // Value = The latest store to that alloca inst that is executed before the detach inst (or its gotstolen handler)
  DenseMap <DetachInst*, DenseMap <AllocaInst*, StoreInst*>> LatestStoreForDetach;

  // The original basic block that needs to be cloned.
  SmallVector<BasicBlock*, 8> bb2clones;
  for( auto &BB : F ) {
    bb2clones.push_back(&BB);
  }

  // Store the basic blocks that holds the sync instruction

  // TODO: Change this to Instruction instead of Basic block
  SmallVector<BasicBlock*, 8> syncBBs;
  SmallVector<SyncInst*, 8> syncInsts;
  for( auto pBB : bb2clones ) {
    if(isa<SyncInst>( pBB->getTerminator())) {
      syncBBs.push_back(pBB);
      syncInsts.push_back(dyn_cast<SyncInst>( pBB->getTerminator()));
    }
  }

  if(true) {
    //if(!EnableStoreLoadForkStorage) {
    for (auto pBB : bb2clones){
      if (DetachInst * DI = dyn_cast<DetachInst>(pBB->getTerminator())){
	BasicBlock * detachBlock = dyn_cast<DetachInst>(DI)->getDetached();
	for( Instruction &II : *detachBlock ) {
	  if( isa<CallInst>(&II) ) {
	    dyn_cast<CallInst>(&II)->getCalledFunction()->addFnAttr(Attribute::Forkable);
	    dyn_cast<CallInst>(&II)->getCalledFunction()->addFnAttr(Attribute::ReturnsTwice);

	  }
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
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
  IRBuilder<> B(C);

  //===================================================================================================

  // Create memory to store location of parallel task in workctx_ar
  B.SetInsertPoint(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());
  // Location of the work
  Value* locAlloc = B.CreateAlloca(TypeBuilder<int, false>::get(M->getContext()), DL.getAllocaAddrSpace(), nullptr, "loc");
  Value* insertPoint  = locAlloc;

  // Indicate that we arrive at the cont path from the the detach block instead from the runtime
  Value* fromSlowPathAlloc  = B.CreateAlloca(TypeBuilder<int, false>::get(M->getContext()), DL.getAllocaAddrSpace(), nullptr, "fromSlowPath");
  insertPoint  = fromSlowPathAlloc;

  // The owner of the work
  Value* ownerAlloc = B.CreateAlloca(IntegerType::getInt32Ty(M->getContext()), DL.getAllocaAddrSpace(), nullptr, "owner");
  insertPoint = ownerAlloc;

  Value* bHaveUnwindAlloc = nullptr;
  if(EnableUnwindOnce) {
    // Create memory to store haveBeenUnwind
    bHaveUnwindAlloc = B.CreateAlloca(IntegerType::getInt1Ty(M->getContext()), DL.getAllocaAddrSpace(), nullptr, "bHaveUnwind");
    if (DisableUnwindPoll)
      insertPoint = bHaveUnwindAlloc;
    else
      insertPoint = B.CreateStore(B.getInt1(0), bHaveUnwindAlloc);
  }

#if 0
  // Move alloca to entry
  for(auto ai : AllocaSet) {
    ai->dump();
    ai->removeFromParent();
    //ai->insertAfter(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());
    insertPoint = B.Insert(ai);
  }
#endif

  // Stores the workcontext value from the slow path entry and will be used to rematerialze the work context in the slowpath
  SSAUpdater SSAUpdateWorkContext;

  // TODO: May not be needed since we use the PreHashTable to get the location of the unwind path
  instrumentPushPop(F, bb2clones);

  // Create the slow path (inserting phi node to capture data from fast path, renaming slow path variable with phi node or fast path variable if needed)
  DenseMap<BasicBlock*, BasicBlock*> syncBB2syncPred;
  if (!seqOrder.empty() || !loopOrder.empty()) {

    //-------------------------------------------------------------------------------------------------
    // If the detach inst has the function inlined, create a wrapper function for it.
    generateWrapperFuncForDetached(F, seqOrder, loopOrder, locAlloc, ownerAlloc, LVout, LVin, VMapSlowPath, VMapGotStolenPath,
				   GotstolenSet, ReachingAllocSet, ReachingAllocToGotstolenSet, LatestStoreForDetach, LatestStoreForGotStolen);

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
    addPotentialJump(F, seqOrder, loopOrder, VMapSlowPath, fromSlowPathAlloc, SSAUpdateWorkContext, ReachingAllocSet);

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

#if 0
	// Debug purpose
	Value * locVal = B.CreateLoad(locAlloc, 1, "locVal");
	Constant* measure_resume_parent = Get_measure_resume_parent(*M);
	B.CreateCall(measure_resume_parent, {locVal});
#endif

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

    // Convert call inst in fast path to multiretcall
    //if(EnableUnwindOnce2) {
    //  convertCallToMultiRetCall(F, bb2clones);
    //}

    // TODO: Remove this as it is no needed
    // Insert a check in the slow path's continue block to check if a thread enters the block from a jump to runtime or from the slowpath's detached block
#if 0
    insertCheckInContBlock(F, seqOrder, loopOrder, VMapSlowPath, fromSlowPathAlloc, RDIBB, SSAUpdateWorkContext);
#endif
    //-------------------------------------------------------------------------------------------------
    // Create the gotstolen handler
    createGotStolenHandler(seqOrder, loopOrder, locAlloc, ownerAlloc, LVout, LVin, VMapSlowPath, VMapGotStolenPath,
			   GotstolenSet, ReachingAllocSet, ReachingAllocToGotstolenSet, LatestStoreForDetach, LatestStoreForGotStolen);

    //====================================================================================================
    if(!EnableMultiRetIR) {
      for(auto pBB : bb2clones) {
	// convert the potential jump to the asm and br
	handlePotentialJump(*pBB);
      }
    }

    // DT Analysis
    //-------------------------------------------------------------------------------------------------
    // Recalculate DT and DF after cloning
    DT.recalculate(F);
    DF.analyze(DT);
    //-------------------------------------------------------------------------------------------------
    if(!EnableSSAUpdateTransformation) {
      // Update the use of the slow instruction and add additional phi node
      DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>> phiMap;
      // For instruction in the fast path that always dominate the slow path (does not need a slow path),
      // replace the use of the slow path inst version with the one from the fast path
      //updateSlowVariables(F, VMapSlowPathReverse, VMapSlowPath, DT, DF, phiMap, RequiredPhiNode, LVin, seqOrder, loopOrder);
      // Fix SSA
      //reconstructSsa(F, VMapSlowPathReverse, VMapSlowPath, DT, DF, phiMap, RequiredPhiNode, LVin, seqOrder, loopOrder);
    } else {
      // Reconstruct SSA
      DenseMap <Instruction *, DenseMap<BasicBlock*, PHINode*>> phiMap;
      updateSlowVariables_2(F, VMapSlowPathReverse, VMapSlowPath, syncBB2syncPred, DT, DF, phiMap, RequiredPhiNode, PhiNodeInserted, LVin, seqOrder, loopOrder, syncInsts);
    }
  }

  // Merge back the slow path back the fast path
  //DenseMap<BasicBlock*, BasicBlock*> syncBB2syncPred;
  if(EnableSSAUpdateTransformation) {

    //mergeSlowPathToFastPath(F, syncInsts, LVin, VMapSlowPath, syncBB2syncPred);

    // Refactor code into a function
    // Reload at every pre.sync basic block
    // Using gvn, the reload in fast path can be removed
    if(!EnableStoreLoadForkStorage) {
      for(auto syncBBi = syncInsts.begin(); syncBBi != syncInsts.end() ; syncBBi++ ) {
	auto syncInst = *syncBBi;
	auto syncBB = syncInst->getParent();
	auto syncSucc = syncInst->getSuccessor(0);

	auto& reachingStore = RSBB[syncBB];

	IRBuilder<> B(C);
	B.SetInsertPoint(syncBB2syncPred[syncSucc]->getFirstNonPHIOrDbgOrLifetime());
	for (auto potAllocaInst : reachingStore) {
	  DEBUG(dbgs() << "PotAllocaInst: " << *potAllocaInst << "\n");

	  AllocaInst* ai = dyn_cast<AllocaInst>(potAllocaInst);
	  if(ai && AllocaSet.find(ai) != AllocaSet.end()) {
	    B.CreateLoad(ai, true);
	  } else {
	    // If the definition uses one of the alloca variable
	    unsigned nOp = potAllocaInst->getNumOperands();
	    for (unsigned i = 0; i<nOp; i++) {
	      auto opVal = potAllocaInst->getOperand(i);
	      AllocaInst* ai2 = dyn_cast<AllocaInst>(opVal);
	      if(ai2 && AllocaSet.find(ai2) != AllocaSet.end()) {
		B.CreateLoad(ai2, true);
	      }
	    }
	  }
	}
      }
    }
    //---------------------------------------------------
  }

  // Get all the detach inst in bbOrder
  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  //-------------------------------------------------------------------------------------------------
  // Multiretcall pathdependent that is in fast path is converted as branch to default, while in slowpath is converted as branch to first indirect bb
  for(auto mrc: MultiRetCallPathSet) {
    auto mrcSlowpath = dyn_cast<MultiRetCallInst>(VMapSlowPath[mrc]);

    BasicBlock* defaultDestFast = mrc->getDefaultDest();
    BasicBlock* indirectDestFast = mrc->getIndirectDest(0);

    BasicBlock* defaultDestSlow = mrcSlowpath->getDefaultDest();
    BasicBlock* indirectDestSlow = mrcSlowpath->getIndirectDest(0);

#if 1

    mrcSlowpath->setDefaultDest(indirectDestSlow);
    mrcSlowpath->setIndirectDest(0, defaultDestSlow);

#else
    // Fastpath mrc goes to default
    auto branch = BranchInst::Create(defaultDestFast);
    // Slowpath mrc goes to 1st indirect dest
    auto branchSlowpath = BranchInst::Create(indirectDestSlow);


    // TODO:FIXME: Need to fix phi node here as well!
    ReplaceInstWithInst(mrcSlowpath, branchSlowpath);
    ReplaceInstWithInst(mrc, branch);


    // Fix phi node in fast path before sync
    for (auto& ii : *defaultDestFast) {
      if(isa<PHINode>(&ii)) {
	// Removie incoming value the indirect dest
	SmallVector<BasicBlock*, 4> removeBBs;
	PHINode* phiN = dyn_cast<PHINode>(&ii);
	unsigned incomingPair = phiN->getNumIncomingValues();
	for(unsigned i = 0; i<incomingPair; i++)  {
	  BasicBlock* incomingBB = phiN->getIncomingBlock(i);
	  if ( incomingBB == indirectDestFast || incomingBB == indirectDestFast->getTerminator()->getSuccessor(0) ) {
	    removeBBs.push_back(incomingBB);
	  }
	}
	for(auto bb: removeBBs) {
	  phiN->removeIncomingValue(bb);
	}
      }
    }

    // Fix phi node in slow path before sync
    for (auto& ii : *defaultDestSlow) {
      if(isa<PHINode>(&ii)) {
	// Removie incoming value the indirect dest
	SmallVector<BasicBlock*, 4> removeBBs;
	PHINode* phiN = dyn_cast<PHINode>(&ii);
	unsigned incomingPair = phiN->getNumIncomingValues();
	for(unsigned i = 0; i<incomingPair; i++)  {
	  BasicBlock* incomingBB = phiN->getIncomingBlock(i);
	  if ( incomingBB == defaultDestSlow ) {
	    removeBBs.push_back(incomingBB);
	  }
	}
	for(auto bb: removeBBs) {
	  phiN->removeIncomingValue(bb);
	}
      }
    }

    // Remove control flow
    IRBuilder<> B(C);
    B.SetInsertPoint(indirectDestFast->getTerminator()->getSuccessor(0)->getTerminator());
    B.CreateUnreachable();
    indirectDestFast->getTerminator()->getSuccessor(0)->getTerminator()->eraseFromParent();


    B.SetInsertPoint(indirectDestFast->getTerminator());
    B.CreateUnreachable();
    indirectDestFast->getTerminator()->eraseFromParent();

    B.SetInsertPoint(defaultDestSlow->getTerminator());
    B.CreateUnreachable();
    defaultDestSlow->getTerminator()->eraseFromParent();

#endif


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
  if(EnableMultiRetIR) {
    SmallVector<BasicBlock*, 4> bbList = {unwindPathEntry};
    auto afterBB = insertPotentialJump(dyn_cast<Instruction>(insertPoint), bbList);

    IRBuilder<> B(dyn_cast<Instruction>(insertPoint)->getNextNode());
    using AsmTypeCallee = void (void);
    FunctionType *killCallee = TypeBuilder<AsmTypeCallee, false>::get(C);
    Value *Asm = InlineAsm::get(killCallee, "", "~{rbx},~{r10},~{r11},~{r12},~{r13},~{r14},~{r15},~{rdi},~{rsi},~{r8},~{r9},~{rdx},~{rcx},~{rax},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    B.CreateCall(Asm);


  } else {
    // Create potential jump from entry to unwindPathEntry
    B.SetInsertPoint(dyn_cast<Instruction>(insertPoint)->getNextNode());
    B.CreateCall(potentialJump, {BlockAddress::get( unwindPathEntry )});
    handlePotentialJump(F.getEntryBlock());
  }


#define LAZYD_POLL
#ifdef LAZYD_POLL
  //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // Instrument prologue and epilogue to insert parallel runtime call
  Constant* push_ss  = Get_push_ss(*M);
  Constant* pop_ss = Get_pop_ss(*M);

  B.SetInsertPoint(dyn_cast<Instruction>(insertPoint)->getNextNode());
  if(!DisablePushPopSeed) {
    // Insert the push of the unwind path entry and polling
    B.CreateCall(push_ss, {BlockAddress::get( unwindPathEntry )});
  }

  // Insert poling
  // Polling @prologue
  if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
    Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_unwind_poll);
    //pollFcn->addFnAttr(Attribute::Forkable);
    auto res = B.CreateCall(pollFcn);
    //res->setTailCall(true);
    DEBUG(dbgs() << F.getName() << " : Polling at prologue\n");
  }

  // Polling @epilogue
  for (auto pBB : bb2clones){
    Instruction * termInst = pBB->getTerminator();
    if(isa<ReturnInst>(termInst) ){
      B.SetInsertPoint(termInst);

      if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
	Function* pollFcn = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_unwind_poll);
	//pollFcn->addFnAttr(Attribute::Forkable);
	if(EnableProperPolling >= 1 ) {
	  auto res = B.CreateCall(pollFcn);
	  res->setTailCall(true);
	  DEBUG(dbgs() << F.getName() << " : Polling at epilogue\n");
	}
      }
    }
  }

  // Polling @loop
  if( (!DisableUnwindPoll && !F.hasFnAttribute(Attribute::ULINoPolling)) ) {
    // Insert Poll in looping
    for (auto L : LI) {
      // Only insert at the inner most loop. Do DFS on nested loop.
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

  // Convert DetachInst, ReattachInst, SyncInst to branch
  convertTapirIrToBr(F);

  //-------------------------------------------------------------------------------------------------
  // Post process: Simplify CFG and verify function
  postProcessCfg(F, AM, DT, AllocaSet, GotstolenSet, ReachingAllocToGotstolenSet, LatestStoreForGotStolen);
  
  // lower grainsize
  SmallVector<IntrinsicInst*, 4 > ii2delete;
  for(auto &BB : F) {
    for(auto &II : BB) {
      if (IntrinsicInst *IntrinsicI = dyn_cast<IntrinsicInst>(&II)) {
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
