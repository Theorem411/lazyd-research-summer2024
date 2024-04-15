/* HandleUnwindPoll function pass
 * Turn builtin into code
 */

#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/MDBuilder.h"
//#include "llvm/IR/TypeBuilder.h"
#include "llvm/Transforms/ULI/HandleUnwindPoll.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#define SV_NAME "uli-handleunwindpoll"
#define DEBUG_TYPE "ULI"

using namespace llvm;

// Copy from unwind_scheduler.h
#define I_RBP 0   // Base pointer
#define I_RIP 1   // Instruction pointer
#define I_RSP 2   // Stack pointer
// Callee register
#define I_RBX 3
#define I_R12 4
#define I_R13 5
#define I_R14 6
#define I_R15 7
// Register
#define I_RDI 8
#define I_RSI 9
#define I_R8 10
#define I_R9 11
#define I_R10 12
#define I_R11 13
#define I_RDX 14
#define I_RCX 15
#define I_RAX 16

#define I_JOINCNT 17 // Join counter
#define I_NEWRSP 18 // New rsp of the parallel task
#define I_OWNER 19 // Who owns the job
#define I_LOC  20 // Location on the parallel task queue of the owner
#define I_ADDRLOC  21 // The address in the stack that store the location of work
#define I_DEQ_CMPLT 22
#define I_SLOWPATH_DEQUE 23
#define I_EXECUTEDBY_OWNER 24
#define WORKCTX_SIZE 64


using unwind_poll_ty = int(void);
using unwind_poll_jmpimm_ty = int(void*);
using unwind_poll_pfor_ty = int(long, long, long*, char*);
using mylongwithoutjmp_callee_ty = void (void**);

/// From CilkAbi.cpp
/// Helper methods for storing to and loading from struct fields.
static Value *GEP(IRBuilder<> &B, Value *Base, int Field) {
  // return B.CreateStructGEP(cast<PointerType>(Base->getType()),
  //                          Base, field);
  return B.CreateConstInBoundsGEP2_32(
      Base->getType()->getScalarType()->getPointerElementType(), Base, 0,
      Field);
}

static Align GetAlignment(const DataLayout &DL, StructType *STy, int Field) {
  return DL.getPrefTypeAlign(STy->getElementType(Field));
}

static void StoreSTyField(IRBuilder<> &B, const DataLayout &DL, StructType *STy,
                          Value *Val, Value *Dst, int Field,
                          bool isVolatile = false,
                          AtomicOrdering Ordering = AtomicOrdering::NotAtomic) {
  StoreInst *S = B.CreateAlignedStore(Val, GEP(B, Dst, Field),
                                      GetAlignment(DL, STy, Field), isVolatile);
  S->setOrdering(Ordering);
}

static Value *LoadSTyField(
    IRBuilder<> &B, const DataLayout &DL, StructType *STy, Value *Src,
    int Field, bool isVolatile = false,
    AtomicOrdering Ordering = AtomicOrdering::NotAtomic) {
  Value *GetElPtr = GEP(B, Src, Field);
  LoadInst *L =
      B.CreateAlignedLoad(GetElPtr->getType()->getPointerElementType(),
                          GetElPtr, GetAlignment(DL, STy, Field), isVolatile);
  L->setOrdering(Ordering);
  return L;
}

#define UNWINDRTS_FUNC(name, CGF) Get__unwindrts_##name(CGF)

// Set the size of the work context length
static cl::opt<int> WorkCtxLen2(
    "set-workctx-len2", cl::init(WORKCTX_SIZE), cl::NotHidden,
    cl::desc("Size of work context length (default = WORKCTX_SIZE)"));

// The type of polling used (ignored if DisableUnwindPoll = true)
static cl::opt<std::string> UnwindPollingType(
    "lazy-poll-lowering", cl::init("unwind-ulifsim"), cl::NotHidden,
    cl::desc("The type of polling used :unwind-steal, unwind-suspend, unwind-only, unwind-ulifsim, nop. Ignored if DisableUnwindPoll is true (default = unwind-steal)"));

// Use builtin to save restore context
static cl::opt<bool> EnableSaveRestoreCtx_2(
    "enable-saverestore-ctx2", cl::init(true), cl::NotHidden,
    cl::desc("Use builtin to save restore context (default = on)"));

// Enable poll epoch
static cl::opt<bool> EnablePollEpoch(
    "enable-poll-epoch", cl::init(false), cl::NotHidden,
    cl::desc("Enable poll epoch (default = off)"));

// Enable poll trace
static cl::opt<bool> EnablePollTrace(
    "enable-poll-trace", cl::init(false), cl::NotHidden,
    cl::desc("Enable poll trace (default = off)"));


#define DEFAULT_GET_LIB_FUNC(name, returnTy, argsTy)				\
  static FunctionCallee Get_##name(Module& M) {                                       \
   LLVMContext &Ctx = M.getContext();                                             \
   return M.getOrInsertFunction( #name,                                            \
				 FunctionType::get(returnTy(Ctx), argsTy(Ctx), false) \
                                  );                                                 \
  }

#define DEFAULT_GET_LIB_FUNC_VOID(name, returnTy)				\
  static FunctionCallee Get_##name(Module& M) {                                       \
   LLVMContext &Ctx = M.getContext();                                             \
   return M.getOrInsertFunction( #name,                                            \
				 FunctionType::get(returnTy(Ctx), {}, false) \
                                  );                                                 \
  }


//using mylongjmp_callee_ty = void (void**);
//DEFAULT_GET_LIB_FUNC(mylongjmp_callee, Type::getVoidTy, )

//using mysetjmp_callee_ty = int (void**);
//DEFAULT_GET_LIB_FUNC(mysetjmp_callee)

//using postunwind_ty = void (void );
DEFAULT_GET_LIB_FUNC_VOID(postunwind, Type::getVoidTy)

//using postunwind_steal_ty = void (void );
DEFAULT_GET_LIB_FUNC_VOID(postunwind_steal, Type::getVoidTy)

//using pollepoch_ty = void (void );
DEFAULT_GET_LIB_FUNC_VOID(pollepoch, Type::getVoidTy)

//using calleverypoll_ty = void (void );
DEFAULT_GET_LIB_FUNC_VOID(calleverypoll, Type::getVoidTy)

//using preunwind_steal_ty = void (void );
DEFAULT_GET_LIB_FUNC_VOID(preunwind_steal, Type::getVoidTy)

//using reduce_threshold_ty = void (void );
DEFAULT_GET_LIB_FUNC_VOID(reduce_threshold, Type::getVoidTy)

//using check_workexists_and_modify_threshold_ty = int (void);
DEFAULT_GET_LIB_FUNC_VOID(check_workexists_and_modify_threshold, Type::getInt32Ty)

//using unwind_workexists_ty = int (void );
DEFAULT_GET_LIB_FUNC_VOID(unwind_workexists, Type::getInt32Ty)

//using POLL_ty = void (int, void*, void*) ;
//DEFAULT_GET_LIB_FUNC_VOID(POLL)

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

static FunctionCallee Get_POLL(Module& M) {
   LLVMContext &Ctx = M.getContext();
   return M.getOrInsertFunction("POLL",
				FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx), PointerType::getInt8PtrTy(Ctx), PointerType::getInt8PtrTy(Ctx)}, false)
                                  );
  }

//using POLL2_ty = void (int, void*, void*, void*) ;
//DEFAULT_GET_LIB_FUNC_VOID(POLL2)

//using stealRequestHandler_poll_ty = void (void*, void*, void*) ;
//DEFAULT_GET_LIB_FUNC_VOID(stealRequestHandler_poll)

static FunctionCallee Get_stealRequestHandler_poll(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("stealRequestHandler_poll", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx), PointerType::getInt8PtrTy(Ctx), PointerType::getInt8PtrTy(Ctx)}, false)
                                  );
}


using unwind_gosteal_ty = void (void );
DEFAULT_GET_LIB_FUNC_VOID(unwind_gosteal, Type::getVoidTy)

//using unwind_suspend_ty = void (void );
DEFAULT_GET_LIB_FUNC_VOID(unwind_suspend, Type::getVoidTy)

namespace {
  struct HandleUnwindPoll : public FunctionPass {

    static char ID; // Pass identification

    HandleUnwindPoll() : FunctionPass(ID) {
    }

    virtual bool doInitialization(Module &M) override {
      return Impl.runInitialization(M);
    }

    bool runOnFunction(Function &F) override {
      doInitialization(*F.getParent());
      return Impl.runImpl(F);

    }

  private:
    HandleUnwindPollPass Impl;

  };

  /// \brief  Create Global variable if it exists, if it doesn't it, create
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
  bool GetOrCreateFunction(const char *FnName, Module& M,
                           FunctionType *FTy, Function *&Fn,
                           Function::LinkageTypes Linkage =
                           Function::InternalLinkage,
                           bool DoesNotThrow = true) {
    LLVMContext &Ctx = M.getContext();
    Fn = M.getFunction(FnName);
    if (Fn)
      return true;

    // Otherwise we have to create it
    //FunctionType *FTy = FunctionType::get(T, false);
    Fn = Function::Create(FTy, Linkage, FnName, &M);
    // Set nounwind if it does not throw.
    if (DoesNotThrow)
      Fn->setDoesNotThrow();
    return false;
  }

  /// \brief MySetJmp
  Function* Get__unwindrts_mysetjmp_callee(Module& M) {
    // Inline assembly to move the callee saved regist to rdi
    Function* Fn = nullptr;
    LLVMContext& Ctx = M.getContext();
    // int (void**);
    FunctionType* mysetjmp_callee_ty = FunctionType::get(Type::getInt32Ty(Ctx), {Type::getInt8Ty(Ctx)->getPointerTo()->getPointerTo()}, false);
    if (GetOrCreateFunction("mysetjmp_callee_llvm", M, mysetjmp_callee_ty, Fn))
      return Fn;


    BasicBlock* Entry = BasicBlock::Create(Ctx, "mysetjmp.entry", Fn);

    Type* Int32Ty = Type::getInt32Ty(Ctx);
    Value* ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
    Value* ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);

    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;
    //using AsmTypeCallee = void (void**);
    FunctionType *FAsmTypeCallee = FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8Ty(Ctx)->getPointerTo()->getPointerTo()}, false);

    InlineAsm* Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rdi\nmovq %rbp, 0(%rdi)\nmovq %rsp, 16(%rdi)\nmovq %rbx, 24(%rdi)\nmovq %r12, 32(%rdi)\nmovq %r13, 40(%rdi)\nmovq %r14, 48(%rdi)\nmovq %r15, 56(%rdi)\n", "r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    IRBuilder<> B(Entry);

    B.CreateCall(Asm, {argsCtx});
    B.CreateRet(ONE);
    return Fn;
  }

  // Store context of work except for the sp
  Function* Get__unwindrts_mysetjmp_callee_nosp(Module& M) {
    // Inline assembly to move the callee saved regist to rdi
    Function* Fn = nullptr;
    LLVMContext& Ctx = M.getContext();
    // int (void**);
    FunctionType* mysetjmp_callee_ty = FunctionType::get(Type::getInt32Ty(Ctx), {Type::getInt8Ty(Ctx)->getPointerTo()->getPointerTo()}, false);
    if (GetOrCreateFunction("mysetjmp_callee_nosp_llvm", M, mysetjmp_callee_ty, Fn))
      return Fn;

    BasicBlock* Entry  = BasicBlock::Create(Ctx, "mysetjmp.entry", Fn);

    Type* Int32Ty = Type::getInt32Ty(Ctx);
    Value* ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
    Value* ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);

    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;
    //using AsmTypeCallee = void (void**);
    FunctionType *FAsmTypeCallee = FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8Ty(Ctx)->getPointerTo()->getPointerTo()}, false);


    InlineAsm* Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rdi\nmovq %rbp, 0(%rdi)\nmovq %rbx, 24(%rdi)\nmovq %r12, 32(%rdi)\nmovq %r13, 40(%rdi)\nmovq %r14, 48(%rdi)\nmovq %r15, 56(%rdi)\n", "r,~{rdi},~{rsi},~{r8},~{r9},~{r10},~{r11},~{rdx},~{rcx},~{rax},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    IRBuilder<> B(Entry);

    B.CreateCall(Asm, {argsCtx});
    //auto OpaqueTrueTy = FunctionType::get(Type::getInt32Ty(Ctx), false);
    //auto OpaqueTrue = InlineAsm::get(OpaqueTrueTy, "xor $0, $0",  "=r,~{dirflag},~{fpsr},~{flags}", false);
    //CallInst* res = B.CreateCall(OpaqueTrue);
    B.CreateRet(ONE);

    return Fn;
  }

  Function *Get__unwindrts_mylongjmp_callee(Module& M) {
    Function* Fn = nullptr;
    LLVMContext& Ctx = M.getContext();
    //void (void**)
    FunctionType* mylongjmp_callee_ty = FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8Ty(Ctx)->getPointerTo()->getPointerTo()}, false);
    if (GetOrCreateFunction("mylongjmp_callee_llvm", M, mylongjmp_callee_ty, Fn))
      return Fn;

    BasicBlock* Entry           = BasicBlock::Create(Ctx, "mylongjmp.entry", Fn);
    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;
    //using AsmTypCallee = void ( void** );
    FunctionType *FAsmTypeCallee = FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8Ty(Ctx)->getPointerTo()->getPointerTo()}, false);

    //Value *Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rdi\nmovq 0(%rdi), %rbp\nmovq 16(%rdi), %rsp\nmovq 24(%rdi), %rbx\nmovq 32(%rdi), %r12\nmovq 40(%rdi), %r13\nmovq 48(%rdi), %r14\nmovq 56(%rdi), %r15\njmpq *8(%rdi)", "r,~{rdi},~{rbx},~{r12},~{r13},~{r14},~{r15},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    InlineAsm* Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rdi\nmovq 0(%rdi), %rbp\nmovq 16(%rdi), %rsp\nmovq 24(%rdi), %rbx\nmovq 32(%rdi), %r12\nmovq 40(%rdi), %r13\nmovq 48(%rdi), %r14\nmovq 56(%rdi), %r15\njmpq *8(%rdi)", "r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    IRBuilder<> B(Entry);
    B.CreateCall(Asm, argsCtx);
    B.CreateRetVoid();
    return Fn;
  }

  Function *Get__unwindrts_mylongwithoutjmp_callee(Module& M) {
    Function* Fn = nullptr;
    LLVMContext& Ctx = M.getContext();
    // void (void**)
    FunctionType* mylongwithoutjmp_callee_ty = FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8Ty(Ctx)->getPointerTo()->getPointerTo()}, false);
    if (GetOrCreateFunction("mylongwithoutjmp_callee_llvm", M, mylongwithoutjmp_callee_ty, Fn))
      return Fn;

    BasicBlock* Entry           = BasicBlock::Create(Ctx, "mywithoutlongjmp.entry", Fn);
    Function::arg_iterator args = Fn->arg_begin();
    Value* argsCtx = &*args;
    //using AsmTypCallee = void ( void** );
    FunctionType *FAsmTypeCallee = FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8Ty(Ctx)->getPointerTo()->getPointerTo()}, false);
    //FunctionType *FAsmTypeCallee = TypeBuilder<AsmTypCallee, false>::get(Ctx);
    InlineAsm* Asm = InlineAsm::get(FAsmTypeCallee, "movq $0, %rdi\nmovq 0(%rdi), %rbp\nmovq 16(%rdi), %rsp\nmovq 24(%rdi), %rbx\nmovq 32(%rdi), %r12\nmovq 40(%rdi), %r13\nmovq 48(%rdi), %r14\nmovq 56(%rdi), %r15\n", "r,~{rdi},~{rbx},~{r12},~{r13},~{r14},~{r15},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);

    IRBuilder<> B(Entry);
    B.CreateCall(Asm, argsCtx);
    B.CreateRetVoid();
    return Fn;
  }


  Function* Get__unwindrts_unwind_poll(Module& M) {
    assert(0 && "Not used");
    Function* Fn = nullptr;
    LLVMContext& Ctx = M.getContext();
    // int (void)
    FunctionType* unwind_poll_ty = FunctionType::get(Type::getInt32Ty(Ctx), {}, false);
    if (GetOrCreateFunction("unwind_poll_llvm", M, unwind_poll_ty, Fn))
      return Fn;

    auto workcontext_ty = ArrayType::get(PointerType::getInt8PtrTy(Ctx), WorkCtxLen2);

    BasicBlock* PollEntry = BasicBlock::Create(Ctx, "poll.entry", Fn);
    BasicBlock* StartUnwind = BasicBlock::Create(Ctx, "start.unwind", Fn);
    BasicBlock* ResumeParent = BasicBlock::Create(Ctx, "resume.parent", Fn);
    //BasicBlock* WorkExists = BasicBlock::Create(Ctx, "work.already.exists", Fn);
    BasicBlock* InitiateUnwind = BasicBlock::Create(Ctx, "initiate.unwind", Fn);

    BasicBlock* ReturnFromPoll = BasicBlock::Create(Ctx, "return.from.poll", Fn);
    BasicBlock* CheckForWork = BasicBlock::Create(Ctx, "check.for.work", Fn);

    BasicBlock* ReduceThreshold = BasicBlock::Create(Ctx, "reduce.threshold", Fn);
    BasicBlock* JoinThreshold = BasicBlock::Create(Ctx, "join.threshold", Fn);

    IRBuilder<> B(PollEntry);

    Value *ONE = B.getInt32(1);
    Value *ZERO = B.getInt32(0);
    Value* ONEBYTE = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 8, false);

    GlobalVariable* platestTime = GetGlobalVariable("latestTime", IntegerType::getInt64Ty(Ctx), M, true);
    GlobalVariable* pthresholdTime = GetGlobalVariable("thresholdTime", IntegerType::getInt64Ty(Ctx), M, true);

    GlobalVariable* prequestCellG = GetGlobalVariable("request_cell", ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), M, true);
    Value* prequestCell = B.CreateConstInBoundsGEP2_64(ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), prequestCellG, 0, 0 );

    if(EnablePollEpoch) {
      FunctionCallee pollepoch = Get_pollepoch(M);
      B.CreateCall(pollepoch);
    }

    if(EnablePollTrace) {
      FunctionCallee calleverypoll = Get_calleverypoll(M);
      B.CreateCall(calleverypoll);
    }

    auto requestCell = B.CreateAlignedLoad(Type::getInt64Ty(Ctx), prequestCell, Align(8));
    auto latestTime = B.CreateAlignedLoad(Type::getInt64Ty(Ctx), platestTime, Align(8));
#if 0
    auto thresholdTime = B.CreateAlignedLoad(Type::getInt64Ty(Ctx), pthresholdTime, Align(8));
#endif
    FunctionCallee unwind_workexists = Get_unwind_workexists(M);

    //auto bWorkExists = B.CreateAlignedLoad(pbWorkExists, 4);
#if 0
    auto incCtr = B.CreateAdd(latestTime, B.getInt64(1));
#else
    auto incCtr = B.CreateSub(latestTime, B.getInt64(1));
#endif
    B.CreateAlignedStore(incCtr, platestTime, Align(8));
#if 0
    auto cmpVal = B.CreateICmpSGE(incCtr, thresholdTime);
#else
    auto cmpVal = B.CreateICmpSLE(incCtr, B.getInt64(0));
#endif
    //auto cmpVal2 = B.CreateICmpEQ(bWorkExists, B.getInt32(0));
    //auto cmpAnd = B.CreateAnd(cmpVal, cmpVal2);
    //auto bWorkExists = B.CreateAlignedLoad(pbWorkExists, 4);


#if 0
    auto cmpReq = B.CreateICmpEQ(requestCell, B.getInt64(-1));
    B.CreateCondBr(cmpReq, JoinThreshold, ReduceThreshold);
#else
    auto cmpReq = B.CreateNot(B.CreateICmpEQ(requestCell, B.getInt64(-1)));
    auto cmpReqOrVal = B.CreateOr(cmpReq, cmpVal);
    B.CreateCondBr(cmpReqOrVal, CheckForWork, ReturnFromPoll);
#endif
    //B.CreateCondBr(cmpReq, JoinThreshold, CheckForWork);
    //B.CreateBr(JoinThreshold);
    B.SetInsertPoint(ReduceThreshold);

    // Hopefully the compiler will optimize this instruction
#if 1
#if 0
    auto halfThreshold = B.CreateMul(thresholdTime, B.getInt64(4));
    halfThreshold = B.CreateSDiv(halfThreshold, B.getInt64(5));

    B.CreateAlignedStore(halfThreshold, pthresholdTime, Align(8));
    B.CreateAlignedStore(B.getInt64(-1), prequestCell, Align(8));
#endif
#else
    FunctionCallee reduce_threshold = Get_reduce_threshold(M);
    B.CreateCall(reduce_threshold);
#endif
    //B.CreateBr(JoinThreshold);
    B.CreateBr(CheckForWork);

    B.SetInsertPoint(JoinThreshold);
    B.CreateCondBr(cmpVal, CheckForWork, ReturnFromPoll);

    B.SetInsertPoint(CheckForWork);
    // Update latest time
#if 0
    B.CreateAlignedStore(B.getInt64(0), platestTime, Align(8));
    auto bWorkExists = B.CreateCall(unwind_workexists);
    auto cmpVal2 = B.CreateICmpEQ(bWorkExists, B.getInt32(0));
    B.CreateCondBr(cmpVal2, InitiateUnwind, ReturnFromPoll);
#else
    FunctionCallee check_workexists_and_modify_threshold = Get_check_workexists_and_modify_threshold(M);
    auto bWorkExists = B.CreateCall(check_workexists_and_modify_threshold);
    auto cmpVal2 = B.CreateICmpEQ(bWorkExists, B.getInt32(0));
    B.CreateCondBr(cmpVal2, InitiateUnwind, ReturnFromPoll);
#endif

    B.SetInsertPoint(InitiateUnwind);

    // mysetjmp_callee(unwindCtx)
    // Store my context
    GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", workcontext_ty, M, true);
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(workcontext_ty, gUnwindContext, 0, 0 );

    FunctionCallee preunwind_steal = Get_preunwind_steal(M);
    B.CreateCall(preunwind_steal);

    if(EnableSaveRestoreCtx_2) {
      auto donothingFcn = Intrinsic::getDeclaration(&M, Intrinsic::donothing);
      auto saveContext = Intrinsic::getDeclaration(&M, Intrinsic::uli_save_context);
      //B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(InitiateUnwind, 1)});
      B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(ResumeParent)});
      B.CreateMultiRetCall((donothingFcn), StartUnwind, ResumeParent, {});

      //Value* savedPc = B.CreateConstGEP1_32(gunwind_ctx, I_RIP);
      //B.CreateStore(BlockAddress::get(InitiateUnwind, 1), savedPc);

    } else {
      assert(0 && "Should use compiler save_restor_ctx");
    }

    // return 1
    B.SetInsertPoint(StartUnwind);

    // Save the ip
    if(EnableSaveRestoreCtx_2) {
      Value* savedPc = B.CreateConstGEP1_32(PointerType::getInt8PtrTy(Ctx), gunwind_ctx, I_RIP);
      B.CreateStore(BlockAddress::get(ResumeParent), savedPc);
    }

    B.CreateRet(ONE);

    // Call postunwind
    B.SetInsertPoint(ResumeParent);
    FunctionCallee postunwind = Get_postunwind(M);
    B.CreateCall(postunwind);
    B.CreateBr(ReturnFromPoll);

    // return 0
    B.SetInsertPoint(ReturnFromPoll);
    B.CreateRet(ZERO);

    return Fn;
  }

  /*
    if(unwind_suspend_llvm()) {
    goto unwindPathEntry;
    }

    New Function for suspend:
    unwind_suspend_llvm() {
    poll.entry:

    // Suspend when threshold
    if(readcyclecounter - load @latestTime >= load @thresholdTime) {
    initiate.unwind:
    store @latestTime <- readcyclecounter

    // If we already have work, just suspend
    if(bWorkExists) {
    unwind_suspend();
    return 0;
    }

    // Otherwise, create the work, then suspend
    mysetjmp_callee (gunwind_ctx);
    gunwind_ctx.ip <- return_here;
    trashed callee register;
    potential jump to return_here;

    start.unwind:
    return 1;

    resume.parent:
    postunwind(); // Runtime call
    unwind_suspend(); // Runtime call
    }
    return.from.poll:
    return 0;
    }

  */

  // Suspend. Only create work if there is no parallel task
  Function* Get__unwindrts_unwind_suspend(Module& M) {
    assert(0 && "Not used");
    Function* Fn = nullptr;
    LLVMContext& Ctx = M.getContext();
    // int (void)
    FunctionType* unwind_poll_ty = FunctionType::get(Type::getInt32Ty(Ctx), {}, false);
    if (GetOrCreateFunction("unwind_suspend_llvm", M, unwind_poll_ty, Fn))
      return Fn;

    auto workcontext_ty = ArrayType::get(PointerType::getInt8PtrTy(Ctx), WorkCtxLen2);

    BasicBlock* PollEntry = BasicBlock::Create(Ctx, "poll.entry", Fn);
    BasicBlock* StartUnwind = BasicBlock::Create(Ctx, "start.unwind", Fn);
    BasicBlock* ResumeParent = BasicBlock::Create(Ctx, "resume.parent", Fn);
    BasicBlock* CheckForWork = BasicBlock::Create(Ctx, "check.for.work", Fn);
    BasicBlock* ImmediateSuspend = BasicBlock::Create(Ctx, "immediate.suspend", Fn);
    BasicBlock* InitiateUnwind = BasicBlock::Create(Ctx, "initiate.unwind", Fn);
    BasicBlock* ReturnFromPoll = BasicBlock::Create(Ctx, "return.from.poll", Fn);
    IRBuilder<> B(PollEntry);

    Value *ONE = B.getInt32(1);
    Value *ZERO = B.getInt32(0);
    Value* ONEBYTE = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 8, false);

    FunctionCallee unwind_suspend = Get_unwind_suspend(M);

    GlobalVariable* platestTime = GetGlobalVariable("latestTime", IntegerType::getInt64Ty(Ctx), M, true);
    GlobalVariable* pthresholdTime = GetGlobalVariable("thresholdTime", IntegerType::getInt64Ty(Ctx), M, true);
    //GlobalVariable* pbWorkExists = GetGlobalVariable("bWorkExists", IntegerType::getInt32Ty(Ctx), M, true);

    auto latestTime = B.CreateAlignedLoad(Type::getInt64Ty(Ctx), platestTime, Align(8));
    auto thresholdTime = B.CreateAlignedLoad(Type::getInt64Ty(Ctx), pthresholdTime, Align(8));
    //auto bWorkExists = B.CreateAlignedLoad(pbWorkExists, 4);

    // Check requirement
    auto incCtr = B.CreateAdd(latestTime, B.getInt64(1));
    B.CreateAlignedStore(incCtr, platestTime, Align(8));
    auto cmpVal = B.CreateICmpSGE(latestTime, thresholdTime);
    B.CreateCondBr(cmpVal, CheckForWork, ReturnFromPoll);

    // Update latest time
    B.SetInsertPoint(CheckForWork);
    FunctionCallee unwind_workexists = Get_unwind_workexists(M);
    auto bWorkExists = B.CreateCall(unwind_workexists);

    B.CreateAlignedStore(B.getInt64(0), platestTime, Align(8));
    auto cmpVal2 = B.CreateICmpEQ(bWorkExists, B.getInt32(0));
    B.CreateCondBr(cmpVal2, InitiateUnwind, ImmediateSuspend);

    B.SetInsertPoint(ImmediateSuspend);
    // Suspend here
    B.CreateCall(unwind_suspend);
    B.CreateBr(ReturnFromPoll);

    // mysetjmp_callee(unwindCtx)
    // Store my context
    B.SetInsertPoint(InitiateUnwind);
    GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", workcontext_ty, M, true);
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(workcontext_ty, gUnwindContext, 0, 0 );

    if(EnableSaveRestoreCtx_2) {
      auto donothingFcn = Intrinsic::getDeclaration(&M, Intrinsic::donothing);
      auto saveContext = Intrinsic::getDeclaration(&M, Intrinsic::uli_save_context);
      B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(ResumeParent)});
      B.CreateMultiRetCall(donothingFcn, StartUnwind, ResumeParent, {});
    } else {
      assert(0 && "EnableSaveRestoreCtx_2 should be 1");
    }

    // return 1
    B.SetInsertPoint(StartUnwind);
    B.CreateRet(ONE);

    // Call postunwind
    B.SetInsertPoint(ResumeParent);
    FunctionCallee postunwind = Get_postunwind(M);
    B.CreateCall(postunwind);

    // Suspend here
    B.CreateCall(unwind_suspend);
    B.CreateBr(ReturnFromPoll);

    // return 0
    B.SetInsertPoint(ReturnFromPoll);
    B.CreateRet(ZERO);

    return Fn;
  }

  /*
  // TODO:
  // If there is a fork statement, increment counter

  if(unwind_communicate_llvm()) {
  goto unwindPathEntry;
  }

  New Function for checking if there is request from other thread:
  unwind_communicate_llvm() {
  poll.entry:

  // There is a request from other worker
  if(request_cell != -1) {
  initiate.unwind:

  // If we already have work, tell the requestor to steal it from the task queue
  if(bWorkExists) {
  unwind_gosteal();
  return 0;
  }

  // Otherwise, create the work, then send the top most work
  mysetjmp_callee (gunwind_ctx);
  gunwind_ctx.ip <- return_here;
  trashed callee register;
  potential jump to return_here;

  start.unwind:
  return 1;

  resume.parent:
  // Give the top work to the requestor
  postunwind_steal(); // Runtime call
  }
  return.from.poll:
  return 0;
  }

  */

  // Use for checking if there is a request for work
  Function* Get__unwindrts_unwind_communicate(Module& M) {
    assert(0 && "Not used");
    Function* Fn = nullptr;
    LLVMContext& Ctx = M.getContext();
    // int (void)
    FunctionType* unwind_poll_ty = FunctionType::get(Type::getInt32Ty(Ctx), {}, false);
    if (GetOrCreateFunction("unwind_communicate_llvm", M, unwind_poll_ty, Fn))
      return Fn;

    auto workcontext_ty = ArrayType::get(PointerType::getInt8PtrTy(Ctx), WorkCtxLen2);

    BasicBlock* PollEntry = BasicBlock::Create(Ctx, "poll.entry", Fn);
    BasicBlock* StartUnwind = BasicBlock::Create(Ctx, "start.unwind", Fn);
    BasicBlock* ResumeParent = BasicBlock::Create(Ctx, "resume.parent", Fn);
    BasicBlock* CheckForWork = BasicBlock::Create(Ctx, "check.for.work", Fn);
    BasicBlock* WorkExists = BasicBlock::Create(Ctx, "work.already.exists", Fn);
    BasicBlock* InitiateUnwind = BasicBlock::Create(Ctx, "initiate.unwind", Fn);
    BasicBlock* ReturnFromPoll = BasicBlock::Create(Ctx, "return.from.poll", Fn);
    IRBuilder<> B(PollEntry);

    Value *ONE = B.getInt32(1);
    Value *ZERO = B.getInt32(0);
    Value* ONEBYTE = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 8, false);

    FunctionCallee unwind_gosteal = Get_unwind_gosteal(M);

    if(EnablePollEpoch) {
      FunctionCallee pollepoch = Get_pollepoch(M);
      B.CreateCall(pollepoch);
    }

    GlobalVariable* pThreadId = GetGlobalVariable("threadId", IntegerType::getInt32Ty(Ctx), M, true);
    GlobalVariable* prequestCellG = GetGlobalVariable("request_cell", ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), M, true);
    auto prequestCell = B.CreateConstInBoundsGEP2_64(ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), prequestCellG, 0, 0 );

    //GlobalVariable* pbWorkExists = GetGlobalVariable("bWorkExists", IntegerType::getInt32Ty(Ctx), M, true);

    auto threadId = B.CreateAlignedLoad(Type::getInt32Ty(Ctx), pThreadId, Align(4));
    auto requestCell = B.CreateAlignedLoad(Type::getInt64Ty(Ctx), prequestCell, Align(8));
    //auto bWorkExists = B.CreateAlignedLoad(pbWorkExists, 4);

    // Check requirement
    auto cmpVal = B.CreateICmpEQ(requestCell, B.getInt64(-1));
    B.CreateCondBr(cmpVal, ReturnFromPoll, CheckForWork);

    // Update latest time
    B.SetInsertPoint(CheckForWork);
    FunctionCallee unwind_workexists = Get_unwind_workexists(M);
    auto bWorkExists = B.CreateCall(unwind_workexists);
    auto cmpVal2 = B.CreateICmpEQ(bWorkExists, B.getInt32(0));
    B.CreateCondBr(cmpVal2, InitiateUnwind, WorkExists);

    B.SetInsertPoint(WorkExists);
    // Already have work, send it
    B.CreateCall(unwind_gosteal);
    B.CreateBr(ReturnFromPoll);

    // mysetjmp_callee(unwindCtx)
    // Store my context
    B.SetInsertPoint(InitiateUnwind);
    GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", workcontext_ty, M, true);
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(workcontext_ty, gUnwindContext, 0, 0 );

    FunctionCallee preunwind_steal = Get_preunwind_steal(M);
    B.CreateCall(preunwind_steal);

    if(EnableSaveRestoreCtx_2) {
      auto donothingFcn = Intrinsic::getDeclaration(&M, Intrinsic::donothing);
      auto saveContext = Intrinsic::getDeclaration(&M, Intrinsic::uli_save_context);
      //auto saveContext = Intrinsic::getDeclaration(&M, Intrinsic::x86_uli_save_callee);
      //B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(InitiateUnwind, 1)});
      B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(ResumeParent)});
      B.CreateMultiRetCall(donothingFcn, StartUnwind, ResumeParent, {});

    } else {
      assert(0 && "EnableSaveRestoreCtx_2 should be 1");
    }

    // return 1
    B.SetInsertPoint(StartUnwind);

    // Save the ip
    if(EnableSaveRestoreCtx_2) {
      Value* savedPc = B.CreateConstGEP1_32(PointerType::getInt8PtrTy(Ctx), gunwind_ctx, I_RIP);
      B.CreateStore(BlockAddress::get(ResumeParent), savedPc);
    }

    B.CreateRet(ONE);

    // Call postunwind
    B.SetInsertPoint(ResumeParent);
    FunctionCallee postunwind_steal = Get_postunwind_steal(M);
    B.CreateCall(postunwind_steal);
    B.CreateBr(ReturnFromPoll);

    // return 0
    B.SetInsertPoint(ReturnFromPoll);
    B.CreateRet(ZERO);

    return Fn;
  }

  // Use for checking if there is a request for work
  Function* Get__unwindrts_unwind_ulifsim(Module& M) {
    assert(0 && "Not used");
    Function* Fn = nullptr;
    LLVMContext& Ctx = M.getContext();
    // int (void)
    FunctionType* unwind_poll_ty = FunctionType::get(Type::getInt32Ty(Ctx), {}, false);
    if (GetOrCreateFunction("unwind_ulifsim_llvm", M, unwind_poll_ty, Fn))
      return Fn;

    auto workcontext_ty = ArrayType::get(PointerType::getInt8PtrTy(Ctx), WorkCtxLen2);

    BasicBlock* PollEntry = BasicBlock::Create(Ctx, "poll.entry", Fn);
    BasicBlock* StartUnwind = BasicBlock::Create(Ctx, "start.unwind", Fn);
    BasicBlock* ResumeParent = BasicBlock::Create(Ctx, "resume.parent", Fn);
    BasicBlock* CheckForWork = BasicBlock::Create(Ctx, "check.for.work", Fn);
    BasicBlock* WorkExists = BasicBlock::Create(Ctx, "work.already.exists", Fn);
    BasicBlock* InitiateUnwind = BasicBlock::Create(Ctx, "initiate.unwind", Fn);
    BasicBlock* ReturnFromPoll = BasicBlock::Create(Ctx, "return.from.poll", Fn);
    IRBuilder<> B(PollEntry);

    Value *ONE = B.getInt32(1);
    Value *ZERO = B.getInt32(0);
    Value* ONEBYTE = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 8, false);

    FunctionCallee unwind_gosteal = Get_unwind_gosteal(M);

    if(EnablePollEpoch) {
      FunctionCallee pollepoch = Get_pollepoch(M);
      B.CreateCall(pollepoch);
    }

    GlobalVariable* pThreadId = GetGlobalVariable("threadId", IntegerType::getInt32Ty(Ctx), M, true);
    GlobalVariable* prequestCellG = GetGlobalVariable("request_cell", ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), M, true);
    auto prequestCell = B.CreateConstInBoundsGEP2_64(ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), prequestCellG, 0, 0 );

    //GlobalVariable* pbWorkExists = GetGlobalVariable("bWorkExists", IntegerType::getInt32Ty(Ctx), M, true);

    auto threadId = B.CreateAlignedLoad(Type::getInt32Ty(Ctx), pThreadId, Align(4));
    auto requestCell = B.CreateAlignedLoad(Type::getInt64Ty(Ctx), prequestCell, Align(8));

    // Check requirement
    auto cmpVal = B.CreateICmpEQ(requestCell, B.getInt64(-1));
    B.CreateCondBr(cmpVal, ReturnFromPoll, CheckForWork);

    // Update latest time
    B.SetInsertPoint(CheckForWork);
    FunctionCallee POLL = Get_POLL(M);
    //auto bWorkExists = B.CreateCall(POLL, B.getInt32(0));

    // FIXME: can not refer to myself blockaddress(self, idx)
    //auto insertPoint = B.CreateMultiRetCall(dyn_cast<Function>(POLL), WorkExists, {InitiateUnwind},
    //             {B.getInt32(0), BlockAddress::get(CheckForWork, 0), BlockAddress::get(CheckForWork, 1)});

    auto insertPoint = B.CreateMultiRetCall(POLL.getFunctionType(), (POLL.getCallee()), WorkExists, {InitiateUnwind},
                                            {B.getInt32(0), BlockAddress::get(WorkExists), BlockAddress::get(InitiateUnwind)});


    B.SetInsertPoint(WorkExists);
    // Already have work, send it
    B.CreateCall(unwind_gosteal);
    B.CreateBr(ReturnFromPoll);

    // mysetjmp_callee(unwindCtx)
    // Store my context
    B.SetInsertPoint(InitiateUnwind);
    GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", workcontext_ty, M, true);
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(workcontext_ty, gUnwindContext, 0, 0 );

    FunctionCallee preunwind_steal = Get_preunwind_steal(M);
    B.CreateCall(preunwind_steal);

    if(EnableSaveRestoreCtx_2) {
      auto donothingFcn = Intrinsic::getDeclaration(&M, Intrinsic::donothing);
      auto saveContext = Intrinsic::getDeclaration(&M, Intrinsic::uli_save_context);
      //B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(InitiateUnwind, 1)});
      B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(ResumeParent)});
      B.CreateMultiRetCall((donothingFcn), StartUnwind, ResumeParent, {});

    } else {
      assert(0 && "EnableSaveRestoreCtx_2 should be 1");
    }

    // return 1
    B.SetInsertPoint(StartUnwind);
    B.CreateRet(ONE);

    // Call postunwind
    B.SetInsertPoint(ResumeParent);
    FunctionCallee postunwind_steal = Get_postunwind_steal(M);
    B.CreateCall(postunwind_steal);
    B.CreateBr(ReturnFromPoll);

    // return 0
    B.SetInsertPoint(ReturnFromPoll);
    B.CreateRet(ZERO);

    return Fn;
  }


  Function* Get__unwindrts_unwind_poll_pfor(Module& M) {
    Function* Fn = nullptr;
    LLVMContext& Ctx = M.getContext();
    // int(long, long, long*, char*)
    Type *VoidPtrTy  = PointerType::getInt8PtrTy(Ctx);
    FunctionType* unwind_poll_pfor_ty = FunctionType::get(Type::getInt32Ty(Ctx), {Type::getInt64Ty(Ctx), Type::getInt64Ty(Ctx), PointerType::getInt64PtrTy(Ctx), PointerType::getInt8PtrTy(Ctx)}, false);
    if (GetOrCreateFunction("unwind_poll_pfor_llvm", M, unwind_poll_pfor_ty, Fn))
      return Fn;
    auto workcontext_ty = ArrayType::get(PointerType::getInt8PtrTy(Ctx), WorkCtxLen2);

    BasicBlock* PollEntry = BasicBlock::Create(Ctx, "poll.entry", Fn);
    BasicBlock* CheckForWork = BasicBlock::Create(Ctx, "check.for.work", Fn);
    BasicBlock* ReturnFromPoll = BasicBlock::Create(Ctx, "return.from.poll", Fn);
    IRBuilder<> B(PollEntry);

    Value *ONE = B.getInt32(1);
    Value *ZERO = B.getInt32(0);
    Value* ONEBYTE = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 8, false);

    FunctionCallee unwind_gosteal = Get_unwind_gosteal(M);

    if(EnablePollEpoch) {
      FunctionCallee pollepoch = Get_pollepoch(M);
      B.CreateCall(pollepoch);
    }

    GlobalVariable* pThreadId = GetGlobalVariable("threadId", IntegerType::getInt32Ty(Ctx), M, true);
    GlobalVariable* prequestCellG = GetGlobalVariable("request_cell", ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), M, true);
    auto prequestCell = B.CreateConstInBoundsGEP2_64(ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), prequestCellG, 0, 0 );

    //GlobalVariable* pbWorkExists = GetGlobalVariable("bWorkExists", IntegerType::getInt32Ty(Ctx), M, true);

    auto threadId = B.CreateAlignedLoad(Type::getInt32Ty(Ctx), pThreadId, Align(4));
    auto requestCell = B.CreateAlignedLoad(Type::getInt64Ty(Ctx), prequestCell, Align(8));

    // Check requirement
    auto cmpVal = B.CreateICmpEQ(requestCell, B.getInt64(-1));
    B.CreateCondBr(cmpVal, ReturnFromPoll, CheckForWork);

    // Update latest time
    B.SetInsertPoint(CheckForWork);
    FunctionCallee stealRequestHandler_poll = Get_stealRequestHandler_poll(M);
    //auto bWorkExists = B.CreateCall(POLL, B.getInt32(0));

    // FIXME: can not refer to myself blockaddress(self, idx)
    //auto insertPoint = B.CreateMultiRetCall(dyn_cast<Function>(POLL), WorkExists, {InitiateUnwind},
    //             {B.getInt32(0), BlockAddress::get(CheckForWork, 0), BlockAddress::get(CheckForWork, 1)});

    //
    //call->getArgOperand();

    Function::arg_iterator args = Fn->arg_begin();

    auto ivValue = &*args;
    auto ivInc = &*(args+1);
    auto ivStorage = &*(args+2);
    auto bHaveUnwindAlloc = &*(args+3);

    //auto nextIteration = B.CreateAdd(ivValue, ivInc);
    B.CreateStore(ivValue, ivStorage, true);

    Value* mySP = getSP(B, *B.GetInsertBlock()->getParent());
    mySP = B.CreateCast(Instruction::IntToPtr, mySP, IntegerType::getInt8Ty(Ctx)->getPointerTo());

    // Get my base pointer
    Value* EIGHT = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 8, false);

    auto addrOfRA = Intrinsic::getDeclaration(&M, Intrinsic::addressofreturnaddress, {VoidPtrTy});
    Value* myRA = B.CreateCall(addrOfRA);
    //myRA = B.CreateBitCast(myRA, IntegerType::getInt8Ty(Ctx)->getPointerTo());
    myRA = B.CreateCast(Instruction::PtrToInt, myRA, IntegerType::getInt64Ty(Ctx));

    Value* myBP = B.CreateSub(myRA, EIGHT);
    myBP = B.CreateCast(Instruction::IntToPtr, myBP, IntegerType::getInt8Ty(Ctx)->getPointerTo());

    auto insertPoint = B.CreateCall(stealRequestHandler_poll,
                                    {BlockAddress::get(CheckForWork), myBP, mySP});

    auto bHaveUnwind = B.CreateLoad(IntegerType::getInt8Ty(Ctx), bHaveUnwindAlloc);
    B.CreateRet(B.CreateZExt(bHaveUnwind, IntegerType::getInt32Ty(Ctx)));
    //B.CreateRet(ZERO);
    //B.CreateBr(ReturnFromPoll);

    B.SetInsertPoint(ReturnFromPoll);
    B.CreateRet(ZERO);

    return Fn;
  }

}


bool HandleUnwindPollPass::detachExists(Function& F) {
  Module* M = F.getParent();

  //for(auto &Fcn : *M) {
    for (auto &BB : F) {
      for (auto it = BB.begin(); it != BB.end(); ++it) {
        auto &instr = *it;

        if(isa<DetachInst>(&instr))
          return true;
      }
    }
    //}
  return false;
}

// Use for checking if there is a request for work
// This simply poll a function
Function* HandleUnwindPollPass::Get__unwindrts_unwind_ulifsim2(Module& M) {
  Function* Fn = nullptr;
  LLVMContext& Ctx = M.getContext();
  const DataLayout &DL = M.getDataLayout();
  //int (void*)
  Type *VoidPtrTy  = PointerType::getInt8PtrTy(Ctx);
  FunctionType* unwind_poll_jmpimm_ty = FunctionType::get(Type::getInt32Ty(Ctx), {PointerType::getInt8PtrTy(Ctx)}, false);


  if (GetOrCreateFunction("unwind_ulifsim2_llvm", M, unwind_poll_jmpimm_ty, Fn))
    return Fn;

  auto workcontext_ty = ArrayType::get(PointerType::getInt8PtrTy(Ctx), WorkCtxLen2);

  BasicBlock* PollEntry = BasicBlock::Create(Ctx, "poll.entry", Fn);
  BasicBlock* CheckForWork = BasicBlock::Create(Ctx, "check.for.work", Fn);
  BasicBlock* ReturnFromPoll = BasicBlock::Create(Ctx, "return.from.poll", Fn);
  IRBuilder<> B(PollEntry);

  Value *ONE = B.getInt32(1);
  Value *ZERO = B.getInt32(0);
  Value* ONEBYTE = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 8, false);

  FunctionCallee unwind_gosteal = Get_unwind_gosteal(M);

  if(EnablePollEpoch) {
    FunctionCallee pollepoch = Get_pollepoch(M);
    B.CreateCall(pollepoch);
  }

#define USE_CHANNEL
  // Check if there is a request
#ifdef USE_CHANNEL
  GlobalVariable* reqlocal = GetGlobalVariable("req_local", RequestChannelTy, M, true);
  //Value* reqchannel2 = B.CreateLoad(reqchannel);
  //Value* reqchannelPerThread = B.CreateInBoundsGEP(reqchannel2, threadId); // &req_channel[threadId]
  //Value* reqchannelPerThreadVal = B.CreateLoad(reqchannelPerThread); // resp_channel[threadId]
  Value* inloop = LoadSTyField(B, DL, RequestChannelTy, reqlocal,
			       RequestChannelFields::inLoop, /*isVolatile=*/false,
			       AtomicOrdering::NotAtomic);
  auto cmpVal = B.CreateICmpEQ(inloop, B.getInt8(0));
#else

  GlobalVariable* pThreadId = GetGlobalVariable("threadId", IntegerType::getInt32Ty(Ctx), M, true);
  GlobalVariable* prequestCellG = GetGlobalVariable("request_cell", ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), M, true);
  auto prequestCell = B.CreateConstInBoundsGEP2_64(ArrayType::get(IntegerType::getInt64Ty(Ctx), 32), prequestCellG, 0, 0 );

  //GlobalVariable* pbWorkExists = GetGlobalVariable("bWorkExists", IntegerType::getInt32Ty(Ctx), M, true);

  auto threadId = B.CreateAlignedLoad(Type::getInt32Ty(Ctx), pThreadId, Align(4));
  auto requestCell = B.CreateAlignedLoad(Type::getInt64Ty(Ctx), prequestCell, Align(8));

  // Check requirement
  auto cmpVal = B.CreateICmpEQ(requestCell, B.getInt64(-1));
#endif
  B.CreateCondBr(cmpVal, ReturnFromPoll, CheckForWork);

  // Update latest time
  B.SetInsertPoint(CheckForWork);
  FunctionCallee stealRequestHandler_poll = Get_stealRequestHandler_poll(M);
  //auto bWorkExists = B.CreateCall(POLL, B.getInt32(0));

  // FIXME: can not refer to myself blockaddress(self, idx)
  //auto insertPoint = B.CreateMultiRetCall(dyn_cast<Function>(POLL), WorkExists, {InitiateUnwind},
  //             {B.getInt32(0), BlockAddress::get(CheckForWork, 0), BlockAddress::get(CheckForWork, 1)});

  Function::arg_iterator args = Fn->arg_begin();
  auto unwindPathEntry = &*args;


  Value* mySP = getSP(B, *B.GetInsertBlock()->getParent());
  mySP = B.CreateCast(Instruction::IntToPtr, mySP, IntegerType::getInt8Ty(Ctx)->getPointerTo());


  // Get my base pointer
  Value* EIGHT = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 8, false);

  auto addrOfRA = Intrinsic::getDeclaration(&M, Intrinsic::addressofreturnaddress, {VoidPtrTy});
  Value* myRA = B.CreateCall(addrOfRA);
  //myRA = B.CreateBitCast(myRA, IntegerType::getInt8Ty(Ctx)->getPointerTo());
  myRA = B.CreateCast(Instruction::PtrToInt, myRA, IntegerType::getInt64Ty(Ctx));

  Value* myBP = B.CreateSub(myRA, EIGHT);
  myBP = B.CreateCast(Instruction::IntToPtr, myBP, IntegerType::getInt8Ty(Ctx)->getPointerTo());

  auto insertPoint = B.CreateCall(stealRequestHandler_poll.getFunctionType(), (stealRequestHandler_poll.getCallee()),
				  //{BlockAddress::get(CheckForWork), myBP, mySP});
				  {unwindPathEntry, myBP, mySP});
  B.CreateBr(ReturnFromPoll);

  B.SetInsertPoint(ReturnFromPoll);
  B.CreateRet(ZERO);

  return Fn;
}


BasicBlock* HandleUnwindPollPass::findUnwindPathEntry(Function& F) {
  BasicBlock* unwindPathEntry = nullptr;
  for (auto &BB : F) {

    for (auto it = BB.begin(); it != BB.end(); ++it) {
      auto &instr = *it;

      auto call = dyn_cast<CallInst>(&instr);
      if (!call) continue;
      auto fn = call->getCalledFunction();
      if (!fn) continue;
      if (fn->getIntrinsicID() != Intrinsic::var_annotation) continue;

      assert(isa<ConstantInt>(call->getArgOperand(3)));
      auto intVal = dyn_cast<ConstantInt>(call->getArgOperand(3));
      unwindPathEntry = (intVal->getSExtValue() == 3) ? &BB : nullptr;

      if(unwindPathEntry) {
        return unwindPathEntry;
      }
    }
  }
  return unwindPathEntry;
}

bool HandleUnwindPollPass::handleUnwindPoll(BasicBlock &BB, BasicBlock* unwindPathEntry) {
  // Search for the unwind path entry, if not found, return
  Module* M = BB.getModule();
  Function* F = BB.getParent();
  LLVMContext& C = BB.getContext();
  IRBuilder<> B(C);

  SmallVector<Instruction*, 4> inst2delete;

  if(!unwindPathEntry || !UnwindPollingType.compare("nop")) {
    if(EnablePollEpoch && (&BB) == &(F->getEntryBlock())) {
      auto instr = BB.getFirstNonPHIOrDbgOrLifetime();
      B.SetInsertPoint(instr);
      FunctionCallee pollepoch = Get_pollepoch(*M);
      auto ci = B.CreateCall(pollepoch);
      //ci->dump();
    }
  }

  // Search for the intrinsic related to unwind polling
  for (auto it = BB.begin(); it != BB.end(); ++it) {
    auto &instr = *it;

    auto call = dyn_cast<CallInst>(&instr);
    if (!call) continue;
    auto fn = call->getCalledFunction();
    if (!fn) continue;
    bool isFcnNotPoll = (fn->getIntrinsicID() != Intrinsic::uli_unwind_poll)
      && (fn->getIntrinsicID() != Intrinsic::uli_unwind_beat)
      && (fn->getIntrinsicID() != Intrinsic::uli_unwind_poll_pfor2);
    if (isFcnNotPoll) continue;

    if(!unwindPathEntry || !UnwindPollingType.compare("nop")) {
      inst2delete.push_back(&instr);
      continue;
    }

    B.SetInsertPoint(&instr);

    BasicBlock* startUnwindStack = BasicBlock::Create(C, "start.unwind.stack", F);
    FunctionCallee unwind_poll = nullptr;
    if((!UnwindPollingType.compare("unwind-only")) ||
       (fn->getIntrinsicID() == Intrinsic::uli_unwind_beat)) {
      unwind_poll = Get__unwindrts_unwind_poll(*M);
    } else if(fn->getIntrinsicID() == Intrinsic::uli_unwind_poll_pfor2) {
      unwind_poll = Get__unwindrts_unwind_poll_pfor(*M);
    } else if(!UnwindPollingType.compare("unwind-suspend")) {
      unwind_poll = Get__unwindrts_unwind_suspend(*M);
    } else if(!UnwindPollingType.compare("unwind-steal")) {
      unwind_poll = Get__unwindrts_unwind_communicate(*M);
    } else if (!UnwindPollingType.compare("unwind-ulifsim-dontuse")) {
      unwind_poll = Get__unwindrts_unwind_ulifsim(*M);
    } else if (!UnwindPollingType.compare("unwind-ulifsim")) {
      unwind_poll = Get__unwindrts_unwind_ulifsim2(*M);
    } else {
      assert(0 && "Unknown unwind-polling-type value");
    }


    CallInst* pollLlvm = nullptr;
    if(fn->getIntrinsicID() == Intrinsic::uli_unwind_poll_pfor2) {
      auto bHaveUnwindAlloc = B.CreateBitCast(call->getArgOperand(3), IntegerType::getInt8Ty(C)->getPointerTo());
      pollLlvm = B.CreateCall(unwind_poll, {call->getArgOperand(0),call->getArgOperand(1), call->getArgOperand(2), bHaveUnwindAlloc});
    } else if(!UnwindPollingType.compare("unwind-ulifsim")) {
      pollLlvm = B.CreateCall(unwind_poll, {BlockAddress::get(unwindPathEntry)});
    } else {
      pollLlvm = B.CreateCall(unwind_poll);
    }
    BasicBlock* bb = pollLlvm->getParent();
    auto cond = B.CreateICmpEQ(pollLlvm, B.getInt32(1));
    auto afterBB = bb->splitBasicBlock(dyn_cast<Instruction>(cond)->getNextNode());
    auto terminator = bb->getTerminator();
    if (!UnwindPollingType.compare("unwind-ulifsim") || fn->getIntrinsicID() == Intrinsic::uli_unwind_poll_pfor2) {
    } else {
      // Update terminator for bb
      auto branch = BranchInst::Create(startUnwindStack, afterBB, cond);
      ReplaceInstWithInst(terminator, branch);
    }

    if(fn->getIntrinsicID() == Intrinsic::uli_unwind_poll_pfor2){
      BasicBlock * returnBB = BasicBlock::Create(C, "return.bb", F);
      auto branch = BranchInst::Create(returnBB, afterBB, cond);
      ReplaceInstWithInst(terminator, branch);
      B.SetInsertPoint(returnBB);
      B.CreateRetVoid();
    }

    // TODO:If unwindPathEntry is not found, just delete the builtin
    B.SetInsertPoint(startUnwindStack);

    // TODO: Kill callee-saved register
    //using AsmTypeCallee = void (void);
    //FunctionType *killCallee = TypeBuilder<AsmTypeCallee, false>::get(C);
    FunctionType *killCallee = FunctionType::get(Type::getVoidTy(C), {}, false);

    InlineAsm* Asm = InlineAsm::get(killCallee, "", "~{rbx},~{r10},~{r11},~{r12},~{r13},~{r14},~{r15},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
    B.CreateCall(Asm);

    B.CreateBr(unwindPathEntry);

    // Remove the polling unwind
    it->eraseFromParent();

    llvm::InlineFunctionInfo ifi;
    llvm::InlineFunction(*pollLlvm, ifi, nullptr, true);

    handleUnwindPoll(*afterBB, unwindPathEntry);

    return true;
  }

  for(auto ii: inst2delete) {
    ii->eraseFromParent();
  }

  return false;
}

bool HandleUnwindPollPass::handleSaveRestoreCtx(BasicBlock &BB) {
  // Search for the unwind path entry, if not found, return
  Module* M = BB.getModule();
  Function* F = BB.getParent();
  LLVMContext& C = BB.getContext();
  IRBuilder<> B(C);

  bool changed = false;

  BasicBlock* unwindPathEntry = nullptr;
  for (auto it = BB.begin(); it != BB.end(); ++it) {
    auto &instr = *it;
    auto call = dyn_cast<CallInst>(&instr);
    if (!call) continue;
    auto fn = call->getCalledFunction();
    if (!fn) continue;
    if ( (fn->getIntrinsicID() != Intrinsic::uli_restore_context)
         && (fn->getIntrinsicID() != Intrinsic::uli_save_context)
         && (fn->getIntrinsicID() != Intrinsic::uli_save_context_nosp) ) continue;


    // For now replace we function call
    if(fn->getIntrinsicID() == Intrinsic::uli_restore_context) {
      // TODO

    } else if(fn->getIntrinsicID() == Intrinsic::uli_save_context) {

    } else if(fn->getIntrinsicID() == Intrinsic::uli_save_context_nosp) {

    }

    changed = true;
  }

  return changed;
}

/// Handle both changereturnaddress and savereturnaddress
bool HandleUnwindPollPass::handleChangeRetAddr(BasicBlock &BB)  {
  // Search for the unwind path entry, if not found, return
  Module* M = BB.getModule();
  Function* F = BB.getParent();
  LLVMContext& C = BB.getContext();
  IRBuilder<> B(C);
  Type *VoidPtrTy  = PointerType::getInt8PtrTy(C);

  SmallVector<Instruction*, 4> inst2delete;
  bool modified = false;
  // Search for the intrinsic related to unwind polling
  for (auto it = BB.begin(); it != BB.end(); ++it) {
    auto &instr = *it;
    auto call = dyn_cast<CallInst>(&instr);
    if (!call) continue;
    auto fn = call->getCalledFunction();
    if (!fn) continue;
    bool isFcnNotChangeRetAddr = (fn->getIntrinsicID() != Intrinsic::uli_change_returnaddress) && ( (fn->getIntrinsicID() != Intrinsic::uli_save_returnaddress));
    if (isFcnNotChangeRetAddr) continue;

    B.SetInsertPoint(&instr);
    modified=true;
    // Collect the intrinsic
    if(fn->getIntrinsicID() == Intrinsic::uli_change_returnaddress) {
      inst2delete.push_back(call);
    } else if(fn->getIntrinsicID() == Intrinsic::uli_save_returnaddress) {
      inst2delete.push_back(call);
    }

  }

  // Modify and delete call to intrisic
  for(auto ii: inst2delete) {
    auto call = dyn_cast<CallInst>(ii);
    auto fn = call->getCalledFunction();
    B.SetInsertPoint(ii);

    if(fn->getIntrinsicID() == Intrinsic::uli_change_returnaddress) {
      auto addrOfRA = Intrinsic::getDeclaration(M, Intrinsic::addressofreturnaddress, {VoidPtrTy});
      Value* myRA = B.CreateCall(addrOfRA);
      myRA = B.CreateBitCast(myRA, IntegerType::getInt64Ty(C)->getPointerTo());
      Value* newAddr = B.CreateCast(Instruction::PtrToInt, call->getArgOperand(0), IntegerType::getInt64Ty(C));
      // Store new returnaddress to location of returnaddress
      B.CreateStore(newAddr, myRA, 1);
    } else if(fn->getIntrinsicID() == Intrinsic::uli_save_returnaddress) {
      auto addrOfRA = Intrinsic::getDeclaration(M, Intrinsic::addressofreturnaddress, {VoidPtrTy});
      Value* myRA = B.CreateCall(addrOfRA);
      myRA = B.CreateBitCast(myRA, IntegerType::getInt64Ty(C)->getPointerTo());
      Value* raValue = B.CreateLoad(IntegerType::getInt64Ty(C), myRA);
      Value* storageLoc = B.CreateBitCast(call->getArgOperand(0), IntegerType::getInt64Ty(C)->getPointerTo());
      // Store return address to stack slot
      B.CreateStore(raValue, storageLoc, 1);
    }

    ii->eraseFromParent();
  }

  return modified;
}


bool HandleUnwindPollPass::handleLazyDInstrumentation(Function &F) {
  Module *M = F.getParent();
  LLVMContext &ctx = F.getContext();
  IRBuilder<> builder(ctx);
  bool Changed = false;

  // iteration variables
  CallInst *CI = nullptr;
  Function *Intrinsic = nullptr;

  // LLVM Types constructors
  IntegerType *I32 = IntegerType::getInt32Ty(ctx);
  IntegerType *I64 = IntegerType::getInt64Ty(ctx);
  Type *I8Ptr = PointerType::get(Type::getInt8Ty(ctx), 0);
  FunctionType *FnTy = FunctionType::get(
                                         /*Result*/Type::getVoidTy(ctx),
                                         /*Params*/{I8Ptr, I64, I64, I32},
                                         /*isVarArg*/false
                                         );
  PointerType *FnPtrTy = PointerType::get(FnTy, 0);

  Value *idx_zero = ConstantInt::get(Type::getInt64Ty(ctx), 0);

  // file and line number using DISubprogram of parent function F
  DISubprogram *Subprogram = F.getSubprogram();

  // collect list of __builtin_uli_lazyd_inst intrinsic for replacement
  SmallVector<Instruction *, 8> Builtin_Uli_Lazyd_Insts;
  for (auto I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    if ((CI = dyn_cast<CallInst>(&*I))
        && (Intrinsic = CI->getCalledFunction())
        && (Intrinsic->getIntrinsicID() == Intrinsic::uli_lazyd_inst))
      {
	// If no subprogram or the second argument is not a nullptr
	Constant *Message= dyn_cast<Constant>(CI->getArgOperand(1));
	assert(Message && "Message is not a constant");
	if(Message->isNullValue()){
	  errs() << "Messsage: is null\n";
	  Message->dump();
	} else {
	  errs() << "Message is not null\n";
	  Message->dump();
	}
	if (Subprogram) {
	  StringRef subpNameStr = Subprogram->getName();
	  // outs() << "found __builtin_uli_lazyd_inst callsite in " << F.getName() << '\n';
	  builder.SetInsertPoint(&*I);
	  // Extract lazydIntrumentLoop function
	  // %0 = bitcast i8* %fnptr to void (i8*, i64, i64, i32)*
	  Value *FnPtr= CI->getArgOperand(0);
	  assert(FnPtr && "fail to retrieve lazydIntrumentLoop from __builtin_uli_lazyd_inst first arg!");
	  Value *Callee = builder.CreateBitCast(
						/*Value*/FnPtr,
						/*DestTy*/FnPtrTy,
						/*Twine:Name*/"instloop"
						);
	  GlobalVariable *globvar = builder.CreateGlobalString(
							       subpNameStr,
							       "file_and_line_number",
							       0 /* Default AddressSpace */,
							       nullptr /* Default Module */
							       );

	  Value *FileAndLineNumber = builder.CreateInBoundsGEP(
							       /*Ty*/globvar->getValueType(),
							       /*Ptr*/globvar,
							       /*IdxList*/{idx_zero, idx_zero}
							       );

	  // extract other operands of __builtin_uli_lazyd_inst
	  Value *TripCount = CI->getArgOperand(2);
	  Value *GranSize = CI->getArgOperand(3);
	  Value *Depth = CI->getArgOperand(4);
	  assert(FileAndLineNumber
		 && TripCount
		 && GranSize
		 && Depth
		 && "__builtin_uli_lazyd_inst has null argument!");

	  // call void %0(i8* file_and_line_number, i64 trip_count, i64 grain_size, i32 depth)
	  auto res = builder.CreateCall(
			     /*FTy*/FnTy,
			     /*Callee*/Callee,
			     /*Args*/{FileAndLineNumber, TripCount, GranSize, Depth}
			     );


	  res->setDebugLoc(CI->getDebugLoc());
	  res->dump();
	  //res->addFnAttr(Attribute::NoInline);
	}
	// delete original intrinsic later
	Builtin_Uli_Lazyd_Insts.push_back(&*I);
	Changed = true;
      }
  }
  // delete replaced intrinsics
  for (auto *I : Builtin_Uli_Lazyd_Insts) {
    I->eraseFromParent();
  }
  return Changed;
}

bool HandleUnwindPollPass::runInitialization(Module &M) {
  auto &C = M.getContext();
  BoolTy = Type::getInt1Ty(C);
  initialized = false;

  // Create the structure for request and response channel
  // Copied from CilkABI.cpp
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

  return true;
}

bool HandleUnwindPollPass::runImpl(Function &F) {
  bool changed = false;

  bool bDetachExists= detachExists(F);
  //assert(!bDetachExists && "Detach still exists");

  if(bDetachExists) {
    for (auto &BB : F) {
      // TODO: handleSaveRestoreCtx is not used, could be removed
      changed |= handleSaveRestoreCtx(BB);
      changed |= handleChangeRetAddr(BB);
    }
    //changed |= handleLazyDInstrumentation(F);
    return changed;
  }



  auto unwindPathEntry = findUnwindPathEntry(F);

  if(unwindPathEntry && !initialized) {
    Module &M = *(F.getParent());
    auto fcn = Get__unwindrts_unwind_ulifsim2(M);
    fcn->addFnAttr(Attribute::NoUnwindPath);

    //auto fcn = UNWINDRTS_FUNC(unwind_poll, M);
    //fcn->addFnAttr(Attribute::NoUnwindPath);
    //fcn = UNWINDRTS_FUNC(unwind_suspend, M);
    //fcn->addFnAttr(Attribute::NoUnwindPath);
    //fcn = UNWINDRTS_FUNC(unwind_communicate, M);
    //fcn->addFnAttr(Attribute::NoUnwindPath);

    //fcn = UNWINDRTS_FUNC(mysetjmp_callee, M);
    //fcn->addFnAttr(Attribute::NoUnwindPath);
    //fcn = UNWINDRTS_FUNC(mysetjmp_callee_nosp, M);
    //fcn->addFnAttr(Attribute::NoUnwindPath);
    //fcn = UNWINDRTS_FUNC(mylongwithoutjmp_callee, M);
    //fcn->addFnAttr(Attribute::NoUnwindPath);
    //fcn = UNWINDRTS_FUNC(mylongjmp_callee, M);
    //fcn->addFnAttr(Attribute::NoUnwindPath);

    initialized = true;
  }

  for (auto &BB : F) {
    // If detach have not been lowered, don't lower the poll
    if(!bDetachExists)
      changed |= handleUnwindPoll(BB, unwindPathEntry);
    // TODO: handleSaveRestoreCtx is not used, could be removed
    changed |= handleSaveRestoreCtx(BB);

    changed |= handleChangeRetAddr(BB);

  }

  changed |= handleLazyDInstrumentation(F);

  return changed;
}

PreservedAnalyses
HandleUnwindPollPass::run(Function &F, FunctionAnalysisManager &AM) {

  runInitialization(*F.getParent());
  // Run on function.
  bool Changed = runImpl(F);
  if (!Changed)
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  // TODO: what analyses are preserved?
  return PA;
}



/////////////////////////////////////////////////////////////

char HandleUnwindPoll::ID = 0;
static RegisterPass<HandleUnwindPoll> X("handleunwindpoll", "Handle unwind poll");


Pass *llvm::createHandleUnwindPollPass() {
  return new HandleUnwindPoll();
}
