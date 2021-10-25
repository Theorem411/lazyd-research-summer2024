/* HandleUnwindPoll function pass
 * Turn builtin into code
 */

#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/TypeBuilder.h"
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
#define WORKCTX_SIZE I_SLOWPATH_DEQUE + 1

using unwind_poll_ty = int(void);
using mylongwithoutjmp_callee_ty = void (void**);

#define UNWINDRTS_FUNC(name, CGF) Get__unwindrts_##name(CGF)

// Set the size of the work context length
static cl::opt<int> WorkCtxLen2(
    "set-workctx-len2", cl::init(WORKCTX_SIZE), cl::NotHidden,
    cl::desc("Size of work context length (default = WORKCTX_SIZE)"));

// The type of polling used (ignored if DisableUnwindPoll = true)
static cl::opt<std::string> UnwindPollingType_2(
    "unwind-polling-type2", cl::init("unwind-only"), cl::NotHidden,
    cl::desc("The type of polling used :unwind-steal, unwind-suspend, unwind-only. Ignored if DisableUnwindPoll is true (default = unwind-only)"));

// Use builtin to save restore context
static cl::opt<bool> EnableSaveRestoreCtx_2(
    "enable-saverestore-ctx2", cl::init(false), cl::NotHidden,
    cl::desc("Use builtin to save restore context (default = off)"));

// Enable poll epoch
static cl::opt<bool> EnablePollEpoch(
    "enable-poll-epoch", cl::init(false), cl::NotHidden,
    cl::desc("Enable poll epoch (default = off)"));

// Enable poll trace
static cl::opt<bool> EnablePollTrace(
    "enable-poll-trace", cl::init(false), cl::NotHidden,
    cl::desc("Enable poll trace (default = off)"));


#define DEFAULT_GET_LIB_FUNC(name)                                      \
  static Constant *Get_##name(Module& M) {                              \
    return M.getOrInsertFunction( #name,                                \
                                  TypeBuilder< name##_ty, false>::get(M.getContext()) \
                                  );                                    \
  }

using mylongjmp_callee_ty = void (void**);
DEFAULT_GET_LIB_FUNC(mylongjmp_callee)

using mysetjmp_callee_ty = int (void**);
DEFAULT_GET_LIB_FUNC(mysetjmp_callee)

using postunwind_ty = void (void );
DEFAULT_GET_LIB_FUNC(postunwind)

using postunwind_steal_ty = void (void );
DEFAULT_GET_LIB_FUNC(postunwind_steal)

using pollepoch_ty = void (void );
DEFAULT_GET_LIB_FUNC(pollepoch)

using calleverypoll_ty = void (void );
DEFAULT_GET_LIB_FUNC(calleverypoll)

using preunwind_steal_ty = void (void );
DEFAULT_GET_LIB_FUNC(preunwind_steal)

using reduce_threshold_ty = void (void );
DEFAULT_GET_LIB_FUNC(reduce_threshold)

using check_workexists_and_modify_threshold_ty = int (void);
DEFAULT_GET_LIB_FUNC(check_workexists_and_modify_threshold)

using unwind_workexists_ty = int (void );
DEFAULT_GET_LIB_FUNC(unwind_workexists)

using unwind_gosteal_ty = void (void );
DEFAULT_GET_LIB_FUNC(unwind_gosteal)

using unwind_suspend_ty = void (void );
DEFAULT_GET_LIB_FUNC(unwind_suspend)

namespace {
  struct HandleUnwindPoll : public FunctionPass {

    static char ID; // Pass identification

    HandleUnwindPoll() : FunctionPass(ID) {
    }

    virtual bool doInitialization(Module &M) override {
      return Impl.runInitialization(M);
    }

    bool runOnFunction(Function &F) override {
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
  template <typename T>
  bool GetOrCreateFunction(const char *FnName, Module& M,
                           Function *&Fn,
                           Function::LinkageTypes Linkage =
                           Function::InternalLinkage,
                           bool DoesNotThrow = true) {
    LLVMContext &Ctx = M.getContext();
    Fn = M.getFunction(FnName);
    if (Fn)
      return true;

    // Otherwise we have to create it
    FunctionType *FTy = TypeBuilder<T, false>::get(Ctx);
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
    if (GetOrCreateFunction<mysetjmp_callee_ty>("mysetjmp_callee_llvm", M, Fn))
      return Fn;

    LLVMContext& Ctx = M.getContext();
    BasicBlock* Entry = BasicBlock::Create(Ctx, "mysetjmp.entry", Fn);

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
    return Fn;
  }


  Function* Get__unwindrts_unwind_poll(Module& M) {
    Function* Fn = nullptr;
    if (GetOrCreateFunction<unwind_poll_ty>("unwind_poll_llvm", M, Fn))
    return Fn;
    LLVMContext& Ctx = M.getContext();
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
    GlobalVariable* prequestCell = GetGlobalVariable("request_cell", IntegerType::getInt64Ty(Ctx), M, true);
    
   
    if(EnablePollEpoch) {
      Constant* pollepoch = Get_pollepoch(M);
      B.CreateCall(pollepoch);
    }

    if(EnablePollTrace) {
      Constant* calleverypoll = Get_calleverypoll(M);
      B.CreateCall(calleverypoll);
    }

    auto requestCell = B.CreateAlignedLoad(prequestCell, 8);
    auto latestTime = B.CreateAlignedLoad(platestTime, 8);
#if 0    
    auto thresholdTime = B.CreateAlignedLoad(pthresholdTime, 8);
#endif    
    Constant* unwind_workexists = Get_unwind_workexists(M);

    //auto bWorkExists = B.CreateAlignedLoad(pbWorkExists, 4);
#if 0
    auto incCtr = B.CreateAdd(latestTime, B.getInt64(1));
#else
    auto incCtr = B.CreateSub(latestTime, B.getInt64(1));
#endif    
    B.CreateAlignedStore(incCtr, platestTime, 8);
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

    B.CreateAlignedStore(halfThreshold, pthresholdTime, 8);
    B.CreateAlignedStore(B.getInt64(-1), prequestCell, 8);
#endif
#else    
    Constant* reduce_threshold = Get_reduce_threshold(M);
    B.CreateCall(reduce_threshold);
#endif
    //B.CreateBr(JoinThreshold);
    B.CreateBr(CheckForWork);

    B.SetInsertPoint(JoinThreshold);
    B.CreateCondBr(cmpVal, CheckForWork, ReturnFromPoll);

    B.SetInsertPoint(CheckForWork);
    // Update latest time
#if 0
    B.CreateAlignedStore(B.getInt64(0), platestTime, 8);
    auto bWorkExists = B.CreateCall(unwind_workexists);
    auto cmpVal2 = B.CreateICmpEQ(bWorkExists, B.getInt32(0));
    B.CreateCondBr(cmpVal2, InitiateUnwind, ReturnFromPoll);
#else
    Constant* check_workexists_and_modify_threshold = Get_check_workexists_and_modify_threshold(M);
    auto bWorkExists = B.CreateCall(check_workexists_and_modify_threshold);
    auto cmpVal2 = B.CreateICmpEQ(bWorkExists, B.getInt32(0));
    B.CreateCondBr(cmpVal2, InitiateUnwind, ReturnFromPoll);    
#endif

    B.SetInsertPoint(InitiateUnwind);

    // mysetjmp_callee(unwindCtx)
    // Store my context
    GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", workcontext_ty, M, true);
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );

    Constant* preunwind_steal = Get_preunwind_steal(M);
    B.CreateCall(preunwind_steal);


    if(!EnableSaveRestoreCtx_2) {
      auto donothingFcn = Intrinsic::getDeclaration(&M, Intrinsic::donothing);
      auto saveContext = Intrinsic::getDeclaration(&M, Intrinsic::x86_uli_save_context);
      //B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(InitiateUnwind, 1)});
      B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(ResumeParent)});
      B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), StartUnwind, ResumeParent, {});

      //Value* savedPc = B.CreateConstGEP1_32(gunwind_ctx, I_RIP);
      //B.CreateStore(BlockAddress::get(InitiateUnwind, 1), savedPc);

    } else {
      Constant* MYSETJMP_CALLEE = Get_mysetjmp_callee(M);
      auto setjmp = B.CreateCall(MYSETJMP_CALLEE, {(gunwind_ctx)});
      auto isEqZero64 = B.CreateICmpEQ(setjmp, B.getInt32(0));
      auto branchInst = B.CreateCondBr(isEqZero64, StartUnwind, ResumeParent);
    }

    // return 1
    B.SetInsertPoint(StartUnwind);
    B.CreateRet(ONE);

    // Call postunwind
    B.SetInsertPoint(ResumeParent);
    Constant* postunwind = Get_postunwind(M);
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
    Function* Fn = nullptr;
    if (GetOrCreateFunction<unwind_poll_ty>("unwind_suspend_llvm", M, Fn))
    return Fn;
    LLVMContext& Ctx = M.getContext();
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

    Constant* unwind_suspend = Get_unwind_suspend(M);

    GlobalVariable* platestTime = GetGlobalVariable("latestTime", IntegerType::getInt64Ty(Ctx), M, true);
    GlobalVariable* pthresholdTime = GetGlobalVariable("thresholdTime", IntegerType::getInt64Ty(Ctx), M, true);
    //GlobalVariable* pbWorkExists = GetGlobalVariable("bWorkExists", IntegerType::getInt32Ty(Ctx), M, true);

    auto latestTime = B.CreateAlignedLoad(platestTime, 8);
    auto thresholdTime = B.CreateAlignedLoad(pthresholdTime, 8);
    //auto bWorkExists = B.CreateAlignedLoad(pbWorkExists, 4);

    // Check requirement
    auto incCtr = B.CreateAdd(latestTime, B.getInt64(1));
    B.CreateAlignedStore(incCtr, platestTime, 8);
    auto cmpVal = B.CreateICmpSGE(latestTime, thresholdTime);
    B.CreateCondBr(cmpVal, CheckForWork, ReturnFromPoll);

    // Update latest time
    B.SetInsertPoint(CheckForWork);
    Constant* unwind_workexists = Get_unwind_workexists(M);
    auto bWorkExists = B.CreateCall(unwind_workexists);

    B.CreateAlignedStore(B.getInt64(0), platestTime, 8);
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
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );

    if(!EnableSaveRestoreCtx_2) {
      auto donothingFcn = Intrinsic::getDeclaration(&M, Intrinsic::donothing);
      auto saveContext = Intrinsic::getDeclaration(&M, Intrinsic::x86_uli_save_context);
      B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(ResumeParent)});
      B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), StartUnwind, ResumeParent, {});
    } else {
      Constant* MYSETJMP_CALLEE = Get_mysetjmp_callee(M);
      auto setjmp = B.CreateCall(MYSETJMP_CALLEE, {(gunwind_ctx)});
      auto isEqZero64 = B.CreateICmpEQ(setjmp, B.getInt32(0));
      auto branchInst = B.CreateCondBr(isEqZero64, StartUnwind, ResumeParent);
    }

    // return 1
    B.SetInsertPoint(StartUnwind);
    B.CreateRet(ONE);

    // Call postunwind
    B.SetInsertPoint(ResumeParent);
    Constant* postunwind = Get_postunwind(M);
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
    Function* Fn = nullptr;
    if (GetOrCreateFunction<unwind_poll_ty>("unwind_communicate_llvm", M, Fn))
    return Fn;
    LLVMContext& Ctx = M.getContext();
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

    Constant* unwind_gosteal = Get_unwind_gosteal(M);
    
    if(EnablePollEpoch) {
      Constant* pollepoch = Get_pollepoch(M);
      B.CreateCall(pollepoch);
    }

    GlobalVariable* pThreadId = GetGlobalVariable("threadId", IntegerType::getInt32Ty(Ctx), M, true);
    GlobalVariable* prequestCell = GetGlobalVariable("request_cell", IntegerType::getInt64Ty(Ctx), M, true);
    //GlobalVariable* pbWorkExists = GetGlobalVariable("bWorkExists", IntegerType::getInt32Ty(Ctx), M, true);

    auto threadId = B.CreateAlignedLoad(pThreadId, 4);
    auto requestCell = B.CreateAlignedLoad(prequestCell, 8);
    //auto bWorkExists = B.CreateAlignedLoad(pbWorkExists, 4);

    // Check requirement
    auto cmpVal = B.CreateICmpEQ(requestCell, B.getInt64(-1));
    B.CreateCondBr(cmpVal, ReturnFromPoll, CheckForWork);

    // Update latest time
    B.SetInsertPoint(CheckForWork);
    Constant* unwind_workexists = Get_unwind_workexists(M);
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
    Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );

    Constant* preunwind_steal = Get_preunwind_steal(M);
    B.CreateCall(preunwind_steal);

    if(!EnableSaveRestoreCtx_2) {
      auto donothingFcn = Intrinsic::getDeclaration(&M, Intrinsic::donothing);
      auto saveContext = Intrinsic::getDeclaration(&M, Intrinsic::x86_uli_save_context);
      //B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(InitiateUnwind, 1)});
      B.CreateCall(saveContext, {B.CreateBitCast(gunwind_ctx, IntegerType::getInt8Ty(Ctx)->getPointerTo()), BlockAddress::get(ResumeParent)});
      B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), StartUnwind, ResumeParent, {});

    } else {
      Constant* MYSETJMP_CALLEE = Get_mysetjmp_callee(M);
      auto setjmp = B.CreateCall(MYSETJMP_CALLEE, {(gunwind_ctx)});
      auto isEqZero64 = B.CreateICmpEQ(setjmp, B.getInt32(0));
      auto branchInst = B.CreateCondBr(isEqZero64, StartUnwind, ResumeParent);
    }

    // return 1
    B.SetInsertPoint(StartUnwind);
    B.CreateRet(ONE);

    // Call postunwind
    B.SetInsertPoint(ResumeParent);
    Constant* postunwind_steal = Get_postunwind_steal(M);
    B.CreateCall(postunwind_steal);
    B.CreateBr(ReturnFromPoll);

    // return 0
    B.SetInsertPoint(ReturnFromPoll);
    B.CreateRet(ZERO);

    return Fn;
  }

}

bool HandleUnwindPollPass::detachExists(Function& F) {
  Module* M = F.getParent();

  for(auto &Fcn : *M) {
    for (auto &BB : Fcn) {
      for (auto it = BB.begin(); it != BB.end(); ++it) {
        auto &instr = *it;

        if(isa<DetachInst>(&instr))
          return true;
      }
    }
  }
  return false;
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

  // Search for the intrinsic related to unwind polling
  for (auto it = BB.begin(); it != BB.end(); ++it) {
    auto &instr = *it;

    auto call = dyn_cast<CallInst>(&instr);
    if (!call) continue;
    auto fn = call->getCalledFunction();
    if (!fn) continue;
    bool isFcnNotPoll = (fn->getIntrinsicID() != Intrinsic::x86_uli_unwind_poll) 
      && (fn->getIntrinsicID() != Intrinsic::x86_uli_unwind_beat) ;
    if (isFcnNotPoll) continue;

    if(!unwindPathEntry) {
      inst2delete.push_back(&instr);
      continue;
    }

    B.SetInsertPoint(&instr);

    BasicBlock * startUnwindStack = BasicBlock::Create(C, "start.unwind.stack", F);
    Constant* unwind_poll = nullptr;
    if((!UnwindPollingType_2.compare("unwind-only")) || 
       (fn->getIntrinsicID() == Intrinsic::x86_uli_unwind_beat)) {
      unwind_poll = Get__unwindrts_unwind_poll(*M);
    } else if(!UnwindPollingType_2.compare("unwind-suspend")) {
      unwind_poll = Get__unwindrts_unwind_suspend(*M);
    } else if(!UnwindPollingType_2.compare("unwind-steal")) {
      unwind_poll = Get__unwindrts_unwind_communicate(*M);
    } else {
      assert(0 && "Unknown unwind-polling-type value");
    }

    auto pollLlvm = B.CreateCall(unwind_poll);
    BasicBlock* bb = pollLlvm->getParent();
    auto cond = B.CreateICmpEQ(pollLlvm, B.getInt32(1));
    auto afterBB = bb->splitBasicBlock(dyn_cast<Instruction>(cond)->getNextNode());

    // Update terminator for bb
    auto terminator = bb->getTerminator();
    auto branch = BranchInst::Create(startUnwindStack, afterBB, cond);
    ReplaceInstWithInst(terminator, branch);

    // TODO:If unwindPathEntry is not found, just delete the builtin

    B.SetInsertPoint(startUnwindStack);
    B.CreateBr(unwindPathEntry);

    // Remove the polling unwind
    it->eraseFromParent();

    llvm::InlineFunctionInfo ifi;
    llvm::InlineFunction(dyn_cast<CallInst>(pollLlvm), ifi, nullptr, true);

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
    if ( (fn->getIntrinsicID() != Intrinsic::x86_uli_restore_context)
         && (fn->getIntrinsicID() != Intrinsic::x86_uli_save_context)
         && (fn->getIntrinsicID() != Intrinsic::x86_uli_save_context_nosp) ) continue;


    // For now replace we function call
    if(fn->getIntrinsicID() == Intrinsic::x86_uli_restore_context) {
      // TODO

    } else if(fn->getIntrinsicID() == Intrinsic::x86_uli_save_context) {

    } else if(fn->getIntrinsicID() == Intrinsic::x86_uli_save_context_nosp) {

    }

    changed = true;
  }

  return changed;
}

bool HandleUnwindPollPass::runInitialization(Module &M) {
  auto &C = M.getContext();
  BoolTy = Type::getInt1Ty(C);
  initialized = false;
  return true;
}

bool HandleUnwindPollPass::runImpl(Function &F) {
  bool changed = false;

  bool bDetachExists= detachExists(F);
  auto unwindPathEntry = findUnwindPathEntry(F);

  if(unwindPathEntry && !initialized) {
    Module &M = *(F.getParent());
    auto fcn = UNWINDRTS_FUNC(unwind_poll, M);
    fcn->addFnAttr(Attribute::NoUnwindPath);
    fcn = UNWINDRTS_FUNC(unwind_suspend, M);
    fcn->addFnAttr(Attribute::NoUnwindPath);
    fcn = UNWINDRTS_FUNC(unwind_communicate, M);
    fcn->addFnAttr(Attribute::NoUnwindPath);

    fcn = UNWINDRTS_FUNC(mysetjmp_callee, M);
    fcn->addFnAttr(Attribute::NoUnwindPath);
    fcn = UNWINDRTS_FUNC(mysetjmp_callee_nosp, M);
    fcn->addFnAttr(Attribute::NoUnwindPath);
    fcn = UNWINDRTS_FUNC(mylongwithoutjmp_callee, M);
    fcn->addFnAttr(Attribute::NoUnwindPath);
    fcn = UNWINDRTS_FUNC(mylongjmp_callee, M);
    fcn->addFnAttr(Attribute::NoUnwindPath);

    initialized = true;
  }

  for (auto &BB : F) {
    // If detach have not been lowered, don't lower the poll
    if(!bDetachExists)
      // Find unwind path entry
      changed |= handleUnwindPoll(BB, unwindPathEntry);

    changed |= handleSaveRestoreCtx(BB);
  }
  return changed;
}

PreservedAnalyses
HandleUnwindPollPass::run(Function &F, FunctionAnalysisManager &AM) {

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
