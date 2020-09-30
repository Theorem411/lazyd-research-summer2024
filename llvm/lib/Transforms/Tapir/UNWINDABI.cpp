//===- UNWINDABI.cpp - Lower Tapir into UNWIND PRSC runtime system calls -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the UNWIND ABI to convert Tapir instructions to calls
// into the user-level-interrupts PRSC library.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Transforms/Tapir/UNWINDABI.h"
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
#include "llvm/IR/MDBuilder.h"
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

#define DEBUG_TYPE "unwindabi"


static SmallVector<Instruction*,2> callInstV;
static SmallVector<Instruction*,2> callInstV2;
static  SmallVector<BasicBlock*,8> contListV;
static SmallVector<Instruction*,8> liveAfterSyncV;
static DenseMap<Instruction*, SyncInst*> mapInstToSyncM;

static DenseMap<SyncInst*, BasicBlock*> sync2bb;

// Map from basic block and instruction in fast path to got stolen handler
static ValueToValueMapTy VMapUNWINDGH;
static ValueToValueMapTy VMapSlowPath; 
static BasicBlock* slowPathPrologue;
static BasicBlock* slowPathEpilogue;
static BasicBlock* unwindPathEntry;
//static BasicBlock* stolenHandlerPathEntry;
//static BasicBlock* slowPathFcn;
//static BasicBlock* restorePath;
static BasicBlock* unwindJumpTableInit;
static BasicBlock* unwindJumpTable;
static BasicBlock* returnInUnwind;

static Value * gworkCtx;
static Value * joinCntr;
static Value * encodedPc;

static int encodedPcCntr = 0;

#define DEFAULT_GET_LIB_FUNC(name)					\
  static Constant *Get_##name(Module& M) {				\
    return M.getOrInsertFunction( #name,				\
				  TypeBuilder< name##_ty, false>::get(M.getContext()) \
				  );					\
  }

using addr_ty = void *;
using workcontext_ty = void * [8];

using push_ss_ty = void (void *);
DEFAULT_GET_LIB_FUNC(push_ss)

using pop_ss_ty = void (void );
DEFAULT_GET_LIB_FUNC(pop_ss)

using dec_ss_ty = void (void );
DEFAULT_GET_LIB_FUNC(dec_ss)

using DISULI_ty = void (void);
DEFAULT_GET_LIB_FUNC(DISULI)

using ENAULI_ty = void (void);
DEFAULT_GET_LIB_FUNC(ENAULI)

using exit_ty = void (int);
DEFAULT_GET_LIB_FUNC(exit)

using mysetjmp_callee_ty = int (void**);
DEFAULT_GET_LIB_FUNC(mysetjmp_callee)

using mylongjmp_callee_ty = void (void**);
DEFAULT_GET_LIB_FUNC(mylongjmp_callee)

using savecontext_ty = int (void**);
DEFAULT_GET_LIB_FUNC(savecontext)

using resume2scheduler_ty = void (void );
DEFAULT_GET_LIB_FUNC(resume2scheduler)

using suspend2scheduler_ty = void (int * );
DEFAULT_GET_LIB_FUNC(suspend2scheduler)

using initworkers_env_ty = void (void );
DEFAULT_GET_LIB_FUNC(initworkers_env)

using deinitworkers_env_ty = void (void );
DEFAULT_GET_LIB_FUNC(deinitworkers_env)

using isunwind_triggered_ty = int (void);
DEFAULT_GET_LIB_FUNC(isunwind_triggered)

using initiate_unwindstack_ty = void (void);
DEFAULT_GET_LIB_FUNC(initiate_unwindstack)

using deinitperworkers_sync_ty = void(int, int);
DEFAULT_GET_LIB_FUNC(deinitperworkers_sync)

using initperworkers_sync_ty = void(int, int);
DEFAULT_GET_LIB_FUNC(initperworkers_sync)

using unwind_poll_ty = int(void);

#define UNWINDRTS_FUNC(name, CGF) Get__unwindrts_##name(CGF)

static GlobalVariable* GetGlobalVariable(const char* GlobalName, Type* GlobalType, Module& M, bool localThread=false){    
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
static bool GetOrCreateFunction(const char *FnName, Module& M,
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

/*
  Refer to uli/cas_ws/lib/unwind_scheduler.h mysetjmp_callee
*/
static Function* Get__unwindrts_mysetjmp_callee(Module& M) {
  // Inline assembly to move the callee saved regist to rdi
  Function* Fn = nullptr;
  if (GetOrCreateFunction<mysetjmp_callee_ty>("mysetjmp_callee_llvm", M, Fn))
    return Fn;

  LLVMContext& Ctx = M.getContext();

  BasicBlock* Entry                 = BasicBlock::Create(Ctx, "mysethjmp.entry", Fn);
  BasicBlock* NormalExit            = BasicBlock::Create(Ctx, "normal.exit", Fn);
  BasicBlock* ThiefExit             = BasicBlock::Create(Ctx, "thief.exit", Fn);

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
  //Value * loadIdx =  B.CreateConstGEP1_32(argsCtx, 1);   
  //B.CreateStore( BlockAddress::get(ThiefExit), loadIdx);
    
  auto OpaqueTrueTy = FunctionType::get(Type::getInt1Ty(Ctx), false);
  auto OpaqueTrue = InlineAsm::get(OpaqueTrueTy, "xor $0, $0",  "=r,~{dirflag},~{fpsr},~{flags}", false);
  Value* res = B.CreateCall(OpaqueTrue);
       
  B.CreateCondBr(res, ThiefExit, NormalExit);
  {
    B.SetInsertPoint(NormalExit);
    B.CreateRet(ZERO);
  }
  {        
    B.SetInsertPoint(ThiefExit);
    B.CreateRet(ONE);
  }

  return Fn;
}


/*
  Refer to uli/cas_ws/lib/unwind_scheduler.h unwind_poll
*/
static Function* Get__unwindrts_unwind_poll(Module& M) {
  Function* Fn = nullptr;
  if (GetOrCreateFunction<unwind_poll_ty>("unwind_poll_llvm", M, Fn))
    return Fn;
  LLVMContext& Ctx = M.getContext();
  
  BasicBlock* PollEntry = BasicBlock::Create(Ctx, "poll.entry", Fn);
  BasicBlock* StartUnwind = BasicBlock::Create(Ctx, "start.unwind", Fn);
  BasicBlock* ResumeParent = BasicBlock::Create(Ctx, "resume.parent", Fn);
  BasicBlock* InitiateUnwind = BasicBlock::Create(Ctx, "initiate.unwind", Fn); 

  IRBuilder<> B(PollEntry);
  
  Value *ONE = B.getInt32(1);
  Value *ZERO = B.getInt32(0);
  
  Constant *ISUNWINDTRIGGERED = Get_isunwind_triggered(M);

  Value *res1 = B.CreateCall(ISUNWINDTRIGGERED);                
  Value *isEqOne = B.CreateICmpEQ(res1, ONE);
  
  B.CreateCondBr(isEqOne, StartUnwind, ResumeParent);
  B.SetInsertPoint(StartUnwind);
  
  Constant *MYSETJMP_CALLEE = UNWINDRTS_FUNC(mysetjmp_callee, M);
  GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", TypeBuilder<workcontext_ty,false>::get(Ctx), M, true);
  Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );
  Value *res2 = B.CreateCall(MYSETJMP_CALLEE, {gunwind_ctx});
  isEqOne = B.CreateICmpEQ(res2, ONE);

  B.CreateCondBr(isEqOne, ResumeParent, InitiateUnwind);

  llvm::InlineFunctionInfo ifi;
  llvm::InlineFunction(dyn_cast<CallInst>(res2), ifi, nullptr, true);              
  
  B.SetInsertPoint(InitiateUnwind);
  Constant *INITIATEUNWINDSTACK = Get_initiate_unwindstack(M);
  B.CreateCall(INITIATEUNWINDSTACK);
  //Value* savedPc = B.CreateConstGEP1_32(gunwind_ctx, 1);   
  //B.CreateStore(BlockAddress::get(ResumeParent), savedPc);    
  B.CreateRet(ONE);

  B.SetInsertPoint(ResumeParent);
  B.CreateRet(ZERO);

  return Fn;    
}


/*
  Refer to uli/cas_ws/lib/unwind_scheduler.h mylongjmp_callee
*/
static Function *Get__unwindrts_mylongjmp_callee(Module& M) {
  Function* Fn = nullptr;
  if (GetOrCreateFunction<mylongjmp_callee_ty>("mylongjmp_callee_llvm", M, Fn))
    return Fn;

  LLVMContext& Ctx = M.getContext();

  BasicBlock* Entry           = BasicBlock::Create(Ctx, "mylongjmp.entry", Fn);    
  Function::arg_iterator args = Fn->arg_begin();
  Value* argsCtx = &*args;

  using AsmTypCallee = void ( void** );
  FunctionType *FAsmTypCallee = TypeBuilder<AsmTypCallee, false>::get(Ctx);

  Value *Asm = InlineAsm::get(FAsmTypCallee, "movq $0, %rdi\nmovq 0(%rdi), %rbp\nmovq 16(%rdi), %rsp\nmovq 24(%rdi), %rbx\nmovq 32(%rdi), %r12\nmovq 40(%rdi), %r13\nmovq 48(%rdi), %r14\nmovq 56(%rdi), %r15\njmpq *8(%rdi)", "r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);
  IRBuilder<> B(Entry);    
  B.CreateCall(Asm, argsCtx);
  B.CreateRetVoid();
  return Fn;
}

/// \brief Get or create a LLVM function for savecontext.
/// It is equivalent to the following C code
/// Refer to uli/cas_ws/lib/scheduler.c savecontext 
///
/// }
static Function *Get__unwindrts_savecontext(Module& M) {
  Function* Fn = nullptr;
  if (GetOrCreateFunction<savecontext_ty>("savecontext_llvm", M, Fn))
    return Fn;

  LLVMContext& Ctx = M.getContext();

  BasicBlock *Entry                 = BasicBlock::Create(Ctx, "unwind.entry", Fn);
  BasicBlock *ThiefEntry            = BasicBlock::Create(Ctx, "unwind.thief.entry", Fn);
  BasicBlock *AttemptUnwinding      = BasicBlock::Create(Ctx, "unwind.attempt.unwinding", Fn);
  BasicBlock *AttemptUnwindCont     = BasicBlock::Create(Ctx, "unwind.attempt.unwind.cont", Fn);
  BasicBlock *ReachTopStack         = BasicBlock::Create(Ctx, "unwind.reach.top.stack", Fn);
  BasicBlock *ReachAlreadyConverted = BasicBlock::Create(Ctx, "unwind.reach.already.converted", Fn);
  BasicBlock *AddrNull              = BasicBlock::Create(Ctx, "unwind.addr.null", Fn);
  BasicBlock *KeepUnwinding         = BasicBlock::Create(Ctx, "unwind.keep.unwinding", Fn);     
  BasicBlock *CheckRA               = BasicBlock::Create(Ctx, "unwind.check.RA", Fn);     
  BasicBlock *FinishUnwinding       = BasicBlock::Create(Ctx, "unwind.finish.unwinding", Fn);     

  Type *Int32Ty = TypeBuilder<int32_t, false>::get(Ctx);
  Value *ZERO = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
  Value *ONE_64T = ConstantInt::get(IntegerType::getInt64Ty(Ctx), 1, /*isSigned=*/false);  
  Value *ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);  
  
  GlobalVariable* gSeed_ptr = GetGlobalVariable("seed_ptr", TypeBuilder<addr_ty*, false>::get(Ctx), M, true); 
  GlobalVariable* gThreadId = GetGlobalVariable("threadId", TypeBuilder<int, false>::get(Ctx), M, true); 
  GlobalVariable* gSeed_bp = GetGlobalVariable("seed_bp", TypeBuilder<addr_ty**, false>::get(Ctx), M);
  GlobalVariable* gUnwindRetAddr = GetGlobalVariable("unwindRetAddr", TypeBuilder<addr_ty, false>::get(Ctx), M, true);
  GlobalVariable* gGotstolenRetAddr = GetGlobalVariable("gotstolenRetAddr", TypeBuilder<addr_ty, false>::get(Ctx), M, true);
  GlobalVariable* gUnwindContext = GetGlobalVariable("unwindCtx", TypeBuilder<workcontext_ty, false>::get(Ctx), M, true);

  IRBuilder<> B(Entry);
  {
      
    ///    unsigned ptr = (seed_ptr - seed_bp[threadId]);      
    Value * gSeed_bpVal = B.CreateLoad(gSeed_bp);    
    Value * gThreadIdVal = B.CreateLoad(gThreadId);
    Value * gSeed_ptrVal = B.CreateLoad(gSeed_ptr);      

    Value * bp_location = B.CreateInBoundsGEP(gSeed_bpVal, gThreadIdVal); 
    Value * gSeed_bpEntry = B.CreateLoad(bp_location);    
    Value* seedOffset = B.CreatePtrDiff(gSeed_ptrVal, gSeed_bpEntry);

    ///    void ** ctx  = (void**) workctx_arr[threadId][ptr]; 
    Function::arg_iterator args = Fn->arg_begin();
    Value* loadIdx1bitcast = &*args;
      
    Constant* MYSETJMP_CALLEE = UNWINDRTS_FUNC(mysetjmp_callee, M);
    Constant* MYLONGJMP_CALLEE = UNWINDRTS_FUNC(mylongjmp_callee, M);
    Value * unwindCtxLoad = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );

    // seed_ptr = 0;
    Value * addPtr = B. CreateConstGEP1_32(gSeed_ptrVal,  0);
    B.CreateStore(addPtr, gSeed_ptr);              
      
    Value* result = B.CreateCall(MYSETJMP_CALLEE, {loadIdx1bitcast});  
    dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);      
      
    Value * isEqOne = B.CreateICmpEQ(result, ONE);        
    B.CreateCondBr(isEqOne, ThiefEntry, AttemptUnwinding);
      
    //Thief entry
    {
      B.SetInsertPoint(ThiefEntry);
      B.CreateRet(ONE);
    }

    // Keep unwinding
    {
      B.SetInsertPoint(AttemptUnwinding);
      // Create another basic block that exits
      
      // void** addrRA = ((void**)*(seed_ptr)); 
      // *addrRa = gotStolenRetAddr;
      Value* pSeedLoad = B.CreateLoad(gSeed_ptr);
      Value* pSeedLoadAdd = B. CreateConstGEP1_32(pSeedLoad,  0);
      Value* seedLoad = B.CreateLoad(pSeedLoadAdd);
      Value* pPseedLoad = B.CreateBitCast(seedLoad, TypeBuilder<addr_ty*, false>::get(Ctx));
      //Value* addrRa = B.CreateLoad(pPseedLoad);
      Value* loadGotStolenAddr = B.CreateLoad(gGotstolenRetAddr);                            
      B.CreateStore(loadGotStolenAddr, pPseedLoad);

      Value* isEqOne = B.CreateICmpEQ(seedOffset, ONE_64T);
      B.CreateCondBr(isEqOne, ReachTopStack, AttemptUnwindCont);
          
      // Reach top of stack
      {
	B.SetInsertPoint(ReachTopStack);
	B.CreateBr(FinishUnwinding);
      }
          
      // Attempt Keep unwinding
      {
	B.SetInsertPoint( AttemptUnwindCont);            

	Value * addPtr = B. CreateConstGEP1_32(gSeed_ptrVal,  -1);
	B.CreateStore(addPtr, gSeed_ptr);        
      
	Value * addPtrVal = B.CreateLoad(addPtr);
	Value * addBitCastVal = B.CreateBitCast(addPtrVal, addPtrVal->getType()->getPointerTo());

	Value * pred1 = B.CreateICmpEQ( addBitCastVal, 
					ConstantPointerNull::get(dyn_cast<PointerType>(addBitCastVal->getType())));              
	B.CreateCondBr(pred1, AddrNull, CheckRA);

	B.SetInsertPoint(AddrNull);
	B.CreateBr(FinishUnwinding);
              
	B.SetInsertPoint(CheckRA);
	Value * loadAddr1  = B.CreateLoad(addBitCastVal);
	Value * loadUnwindAddr1 = B.CreateLoad(gUnwindRetAddr);              
	Value * pred2 = B.CreateICmpEQ(loadAddr1, loadUnwindAddr1);                           

	B.CreateCondBr(pred2, KeepUnwinding, ReachAlreadyConverted);
	{
	  B.SetInsertPoint( ReachAlreadyConverted );
	  B.CreateBr(FinishUnwinding);
	}

	{
	  B.SetInsertPoint( KeepUnwinding );           
	  B.CreateRet(ZERO);
	}
      }
          
      // Finish Unwinding
      {
	B.SetInsertPoint(FinishUnwinding);
	Value * result = B.CreateCall(MYLONGJMP_CALLEE, {unwindCtxLoad});
	dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);
	llvm::InlineFunctionInfo ifi;
	llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);
	B.CreateBr(ThiefEntry);
      }
    }

    llvm::InlineFunctionInfo ifi;
    llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);

  }  
  Fn->addFnAttr(Attribute::InlineHint);
  return Fn;
}

static void handlePotentialJump(Instruction* instr, BasicBlock * BB) {
    auto call = dyn_cast<CallInst>(instr);
    if (!call) return;
    auto fn = call->getCalledFunction();
    if (!fn) return;
    if (fn->getIntrinsicID() != Intrinsic::x86_uli_potential_jump)return;
    auto afterPotentialJump = instr->getNextNode(); 

    auto BA = dyn_cast<BlockAddress>(call->getArgOperand(0));
    assert(BA);
    auto InletBlock = BA->getBasicBlock();


    instr->eraseFromParent();
    auto afterBB = BB->splitBasicBlock(afterPotentialJump);
    
    auto terminator = BB->getTerminator();

    auto &C = BB->getParent()->getContext();
    auto BoolTy = Type::getInt1Ty(C);

    auto OpaqueTrueTy = FunctionType::get(BoolTy, false);
    auto OpaqueTrue = InlineAsm::get(OpaqueTrueTy, "xor $0, $0",  "=r,~{dirflag},~{fpsr},~{flags}", false);

    auto cond = CallInst::Create(OpaqueTrue, "", terminator);

    auto branch = BranchInst::Create(InletBlock, afterBB, cond);
    branch->setMetadata(LLVMContext::MD_prof, MDBuilder(branch->getContext()).createBranchWeights(1, 99));

    ReplaceInstWithInst(terminator, branch);

}

static bool isNonPHIOrDbgOrLifetime(Instruction * I) { 
  if (isa<PHINode>(I) || isa<DbgInfoIntrinsic>(I))
    return false;
  
  if (auto *II = dyn_cast<IntrinsicInst>(I))
    if (II->getIntrinsicID() == Intrinsic::lifetime_start ||
	II->getIntrinsicID() == Intrinsic::lifetime_end || 
	II->getIntrinsicID() == Intrinsic::syncregion_start)
      return false;

  return true;

}


void UNWINDABI::createSync(SyncInst &SI, ValueToValueMapTy &DetachCtxToStackFrame) {         
  
  outs() << "I am in create Sync\n";
  SI.dump();
  outs() << "-------------------\n";
  
  BasicBlock * succ = SI.getSuccessor(0);        

  // Replace the slow path sync isnt with a branch to fast sync's successor.
  // TODO: Create the slow path
  BasicBlock* BB = SI.getParent();
  Function* F = BB->getParent();
  LLVMContext& C = F->getContext();
  Instruction* slowSI = dyn_cast<Instruction>(VMapSlowPath[&SI]);   
  
  // Jump back to the fast path
#if 1
  BasicBlock * restorePath = sync2bb[&SI];
  createSlowPathEpilogue(*(slowSI->getParent()->getParent()), slowSI, gworkCtx, restorePath);  

  Instruction* iterm = restorePath->getTerminator();                  
  BranchInst* resumeBr = BranchInst::Create(succ);  
  ReplaceInstWithInst(iterm, resumeBr);
#endif    
  
  DT->recalculate( *(SI.getParent()->getParent()) );
  // From top sync to bottom sync
  for(auto II : liveAfterSyncV) {
    
    Instruction * phiRes = dyn_cast<Instruction>(VMapSlowPath[II]);
    outs() << "Cont list\n";
    auto cr = contListV.rbegin(); 
    auto ce = contListV.rend();
    for (; cr != ce; ) {
      BasicBlock *contBB = *cr;
      ++cr;
          
      if(DT->dominates(II, contBB )){
	II->dump();
	contBB->dump();
      
	// Create phi node
	BasicBlock *contBBslow = dyn_cast<BasicBlock>(VMapSlowPath[contBB]);
	IRBuilder<> B(contBBslow->getFirstNonPHIOrDbgOrLifetime());        
	auto phiNode = B.CreatePHI(II->getType(), 2);  

	outs () << "Recursive basic block\n";
	for (auto it = pred_begin(contBBslow), et = pred_end(contBBslow); it!=et; ++it){
	  BasicBlock* pred = *it;
	  phiRes->dump();
	  pred->dump();
	  slowPathPrologue->dump();
	  if(isa<DetachInst>(pred->getTerminator()) || isa<ReattachInst>(pred->getTerminator())) {
	  //if (DT->dominates(phiRes, pred) ){
	    // Slow
	    outs() << "Slow Basic block : \n";
	    phiNode->addIncoming(phiRes, pred);
	    phiNode->dump();

	  } else {
	    outs() << "Fast Basic block : \n";
	    //phiNode->addIncoming(II, pred);
	    phiNode->addIncoming(UndefValue::get(II->getType()), pred);
	    phiNode->dump();	    
	  }
	}
	outs() << "------------------------\n";
	
	Value::use_iterator UI = phiRes->use_begin(), E = phiRes->use_end();
	for (; UI != E;) {
	  Use &U = *UI;
	  ++UI;
	  auto *Usr = dyn_cast<Instruction>(U.getUser());
	  // FIXME: Remove if hack, need to fix DT
	  if (Usr && !isa<PHINode>(Usr) && !isa<DetachInst>(Usr->getParent()->getTerminator()) )
	      //( DT->dominates(phiNode, Usr) || contBBslow == Usr->getParent()) )            
	    U.set(phiNode);	
	
	  SmallVector< BasicBlock *, 8 > Result;
	  DT->getDescendants (II->getParent(), Result);
	  
	  outs() << "Node dominated by :\n";
	  phiNode->getParent()->dump();
	  outs() << "Res:\n";
	  for(auto pBB : Result) {
	    pBB->dump();
	  }
	  
	}
	
	phiRes = phiNode; 
	
      }
    }
    outs() << "---------------\n";


    if(mapInstToSyncM[II] = &SI){
      outs() << "Create PhiNode: \n";
      II->dump();
      II->getType()->dump();
      (dyn_cast<Instruction>(VMapSlowPath[II]))->dump();
      outs() << "In sync: \n";
      SI.dump();
     
      IRBuilder<> B(succ->getFirstNonPHIOrDbgOrLifetime());        
      auto phiNode = B.CreatePHI(II->getType(), 2);  
      
      for (auto it = pred_begin(succ), et = pred_end(succ); it!=et; ++it){
	BasicBlock* pred = *it;
	if (DT->dominates(phiRes, pred)){
	  outs() << "Basic block : \n";
	  pred->dump();
	  outs() << "Instruction in Phi Slow: \n";
	  (dyn_cast<Instruction>(VMapSlowPath[II]))->dump();
	  phiNode->addIncoming(phiRes, pred);
	} else {
	  outs() << "Basic block : \n";
	  pred->dump();
	  outs() << "Instruction in Phi Fast: \n";
	  II->dump();
	  phiNode->addIncoming(II, pred);	 
	}
      }

#if 1        
      Value::use_iterator UI = II->use_begin(), E = II->use_end();
      for (; UI != E;) {
	Use &U = *UI;
	++UI;
	auto *Usr = dyn_cast<Instruction>(U.getUser());
	if (Usr && !isa<PHINode>(Usr) && 
	    (DT->dominates(succ->getFirstNonPHIOrDbgOrLifetime(), Usr->getParent()) || succ == Usr->getParent()) )            
	  U.set(phiNode);
      }
#endif
	                
    }
  }

  // Fast Path
  // ----------------------------------------------
  {
    // Create a phi node for the return result of the last child
#if 0
    if(!callInstV.empty()) {
      IRBuilder<> B(succ->getFirstNonPHIOrDbgOrLifetime());        
      CallInst* CI = dyn_cast<CallInst>(callInstV.front());
      Function * fcn = CI->getCalledFunction();
        
      auto phiNode = B.CreatePHI(fcn->getReturnType(), 2);  
      for (auto it = pred_begin(succ), et = pred_end(succ); it!=et; ++it){
	BasicBlock* pred = *it;
          
	// FIXME: Use analysis from domintor tree instead of assuming a fix relation ship between basic block basic block
	if(pred == callInstV.front()->getParent()){
	  phiNode->addIncoming(callInstV.front(), callInstV.front()->getParent());
	} else {
	  phiNode->addIncoming(callInstV.back(), pred);
	}
	          
      }
        
      Value::use_iterator UI = CI->use_begin(), E = CI->use_end();
      for (; UI != E;) {
	Use &U = *UI;
	++UI;
	auto *Usr = dyn_cast<Instruction>(U.getUser());
	if (Usr && !isa<PHINode>(Usr) && Usr->getParent() == succ )            
	  U.set(phiNode);
      }
    }
#endif
  }  

#if 0
  // Create a phi node for a load instruction in the restore path
  for(auto &II: *succ) {
    if(isa<LoadInst>(&II)){
      IRBuilder<> B(succ->getFirstNonPHIOrDbgOrLifetime());
      auto phiNode = B.CreatePHI(dyn_cast<LoadInst>(&II)->getType(), 2);  

      for (auto it = pred_begin(succ), et = pred_end(succ); it!=et; ++it){
	BasicBlock* pred = *it;
	
	// FIXME: Use analysis from domintor tree instead of assuming a fix relation ship between basic block basic block
	if(pred == callInstV.front()->getParent()){
	  phiNode->addIncoming(callInstV2.front(), callInstV.front()->getParent());
	} else {
	  phiNode->addIncoming(callInstV2.back(), pred);
	}
          
      }
        
      Value::use_iterator UI = II.use_begin(), E = II.use_end();
      for (; UI != E;) {
	Use &U = *UI;
	++UI;
	auto *Usr = dyn_cast<Instruction>(U.getUser());
	if (Usr && !isa<PHINode>(Usr) && Usr->getParent() == succ )            
	  U.set(phiNode);
      }
      
    }
  }  
#endif  
  return;
}

BasicBlock * UNWINDABI::createGotStolenHandler(DetachInst& Detach,  SyncInst * detachSyncPair) {
  BasicBlock* curBB = Detach.getParent();
  Function* F = curBB->getParent();
  Module* M = F->getParent();
  LLVMContext& C = F->getContext();
  
  Constant* suspend2scheduler = Get_suspend2scheduler(*M);
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);

  BasicBlock * detachBB = Detach.getDetached(); 
  // Clone detach Block 
#if 0
  // Create label after the call inst. This will be the got stolen handler
  // -------------------------------------------------------------------------
  DebugInfoFinder DIFinder;      
  DISubprogram *SP = F->getSubprogram();
  if (SP) {
    //assert(!MustCloneSP || ModuleLevelChanges);
    // Add mappings for some DebugInfo nodes that we don't want duplicated
    // even if they're distinct.
    auto &MD = VMapUNWINDGH.MD();
    MD[SP->getUnit()].reset(SP->getUnit());
    MD[SP->getType()].reset(SP->getType());
    MD[SP->getFile()].reset(SP->getFile());  
    MD[SP].reset(SP); 
  }        
    
  // Perform the actual cloning
  BasicBlock * stolenHandlerPathEntry = CloneBasicBlock(detachBB, VMapUNWINDGH, ".gotstolen", F, nullptr, &DIFinder);
  VMapUNWINDGH[detachBB] = stolenHandlerPathEntry;        
     
  // --------------------------------------------------------------
  // Remap the cloned instruction
  for (Instruction &II : *stolenHandlerPathEntry) {
    RemapInstruction(&II, VMapUNWINDGH, RF_IgnoreMissingLocals, nullptr, nullptr);
  }
#else

  BasicBlock * stolenHandlerPathEntry = BasicBlock::Create(C, "gotstolenhandler", F);

#endif
  // Add potential jump from detachBB to got stolen handler
  // Add potential jump after "spawn to fib" to avoid merging the gotstolen handler and the detachBlock
  IRBuilder<> builder(detachBB->getTerminator()); 
  builder.CreateCall(potentialJump, {BlockAddress::get( stolenHandlerPathEntry )});        

#if 0
  builder.SetInsertPoint(stolenHandlerPathEntry->getTerminator());
#else
  builder.SetInsertPoint(stolenHandlerPathEntry);
#endif
        
  // Perform synchronizatoin here        
  builder.CreateCall(suspend2scheduler, {ConstantPointerNull::get(builder.getInt32Ty()->getPointerTo())});        

#if 0
  Instruction* iterm = stolenHandlerPathEntry->getTerminator();                
  //BranchInst* resumeBr = BranchInst::Create(unwindPathEntry);
  BranchInst* resumeBr = BranchInst::Create(slowPathPrologue);
  ReplaceInstWithInst(iterm, resumeBr);
#else
  //builder.CreateBr(slowPathPrologue);        
  builder.CreateUnreachable();
#endif 

  //Split basic block here. Used as hack to reload join counter in -0O
  //stolenHandlerPathEntry->splitBasicBlock(stolenHandlerPathEntry->getTerminator()->getPrevNode());

  for( Instruction &II : *detachBB){
    if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->hasFnAttribute(Attribute::Forkable)){	
      callInstV2.push_back(&II);
      // Associate callsite instruction with got-stolen handler
      M->CallStealMap[&II].stolenHandler = stolenHandlerPathEntry;          
      break;        
    }
  } 
  M->StolenHandlerExists[stolenHandlerPathEntry] = true;
    
  SmallVector<Instruction *, 4> inst2delete;
  
  // Look for the store instruction
  for (Instruction &II : *detachBB) {
    if(isa<StoreInst>(&II)){
      inst2delete.push_back(&II);      
      break;
    }
  }

#if 0
  for(Instruction *II: inst2delete){
    II->eraseFromParent();
  }
    
  for (Instruction &II : *stolenHandlerPathEntry) {
    if(isa<StoreInst>(&II)){
      StoreInst* storeAfterFork = dyn_cast<StoreInst>(&II);
      //builder.SetInsertPoint(&II);
      storeAfterFork->setVolatile(true);
      //builder.CreateCall(STORE2MEM, {storeAfterFork->getValueOperand(), storeAfterFork->getPointerOperand()});
     
      // Create a load instruction
      if(restorePath->getTerminator()){
	builder.SetInsertPoint(restorePath->getTerminator());
      } else {
	builder.SetInsertPoint(restorePath);
      }
      LoadInst* LI = builder.CreateLoad(storeAfterFork->getValueOperand()->getType(), storeAfterFork->getPointerOperand());
      LI->setVolatile(true);
      callInstV2.push_back(LI);
    }
  }
#else
  // Look for the store instruction
  Instruction * strInst = inst2delete.front()->clone(); 
  
  StoreInst* storeAfterFork = dyn_cast<StoreInst>(strInst);
  storeAfterFork->insertBefore(stolenHandlerPathEntry->getFirstNonPHIOrDbgOrLifetime());
  storeAfterFork->setVolatile(true);
  // Create a load instruction

  if (!sync2bb.lookup(detachSyncPair)){
    sync2bb[detachSyncPair] = BasicBlock::Create(C, "restore.path", F); 
    builder.SetInsertPoint(sync2bb[detachSyncPair]);
    builder.CreateUnreachable();
  }
  builder.SetInsertPoint(sync2bb[detachSyncPair]->getTerminator());
  

  sync2bb[detachSyncPair]->dump();
  LoadInst* LI = builder.CreateLoad(storeAfterFork->getValueOperand()->getType(), storeAfterFork->getPointerOperand());
  LI->setVolatile(true);
  callInstV2.push_back(LI);
  

#endif

  return stolenHandlerPathEntry;
}

BasicBlock * UNWINDABI::createSlowPathFcn(DetachInst& Detach) {
  BasicBlock* curBB = Detach.getParent();
  Function* F = curBB->getParent();    
    
  BasicBlock* slowPathFcn = nullptr;
  if(!isTre) {
    BasicBlock * contBB = Detach.getContinue(); 
    slowPathFcn = dyn_cast<BasicBlock>(VMapSlowPath[contBB]);
     
    for(Instruction &II : *contBB) {
      // Look for potential call used to construct the phi node in the resume instruction
      // Has to be a forkable function
      if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->hasFnAttribute(Attribute::Forkable) 
	 && !dyn_cast<CallInst>(&II)->getCalledFunction()->getReturnType()->isVoidTy()) {
	callInstV.push_back(dyn_cast<CallInst>(&II));
	callInstV.push_back(dyn_cast<CallInst>(VMapSlowPath[&II]));
      } 
    }
        
    //Instruction* itermSlowPathPrologue = slowPathPrologue->getTerminator();      
    //BranchInst* resume2SlowPathFcn = BranchInst::Create(slowPathFcn);
    //ReplaceInstWithInst(itermSlowPathPrologue, resume2SlowPathFcn);
    
    //Instruction* itermSlowPathFcn = slowPathFcn->getTerminator();
    //BranchInst* resume2slowPathEpilogue = BranchInst::Create(slowPathEpilogue);        
    //ReplaceInstWithInst(itermSlowPathFcn, resume2slowPathEpilogue);
    
  } else {
    LLVMContext& C = F->getContext();
    
    slowPathFcn = BasicBlock::Create(C, "before.tre.slowpath", F);      
    
    BranchInst* resume2SlowPathFcn = BranchInst::Create(slowPathFcn);
    Instruction* itermSlowPathPrologue = slowPathPrologue->getTerminator();  
    ReplaceInstWithInst(itermSlowPathPrologue, resume2SlowPathFcn);

    IRBuilder<> B(slowPathFcn);
    B.SetCurrentDebugLocation(Detach.getDebugLoc());
    
    SmallVector<Value *, 4> argV;        
    for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E; ++I) {
      // Get the use of the argument, if it is used in a phi node, get the other value
      bool useOtherVal = false;
      Value *otherVal = nullptr;
      for (User *U : I->users()) {
	if (U && isa<PHINode>(U)) {            
	  PHINode* phiNode = dyn_cast<PHINode>(U);
	  unsigned incomingEdge = phiNode->getNumIncomingValues();
	  for(int i=0; i<incomingEdge; i++) {
	    BasicBlock * blockIn = phiNode->getIncomingBlock(i);
	    if(blockIn == Detach.getContinue()){
	      otherVal = phiNode->getIncomingValue(i);
	      useOtherVal = true;
	      break;
	    }
	  }
	}                    
      } 
      if(useOtherVal) {
	argV.push_back(otherVal);
      } else {
	argV.push_back(I);
      }
    }
    B.CreateCall(F, argV);
    B.CreateBr(slowPathEpilogue);        
  }  

  return slowPathFcn;
}

void UNWINDABI::createFastPath(DetachInst& Detach) {
  // Add the prologue at beginning of the deattach block
  BasicBlock* curBB = Detach.getParent();
  Function* F = curBB->getParent();
  Module* M = F->getParent();
  LLVMContext& C = M->getContext();

  BasicBlock* bb = nullptr;
  Instruction* term = nullptr;
  SmallVector<BasicBlock*, 8> bbList;
  DenseMap<BasicBlock *, bool> haveVisited;

  BasicBlock* detachBB = Detach.getDetached();        
  Value* OneByte = ConstantInt::get(IntegerType::getInt64Ty(C), 8, false);

  // Common Used Function
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
  Function* getSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);

  Constant* PUSH_SS = Get_push_ss(*M);
  Constant* POP_SS = Get_pop_ss(*M);

  IRBuilder<> fastBuilder(detachBB->getFirstNonPHIOrDbgOrLifetime()); 
        
  // Build the Fast Path Prologue

  // Add the push_ss instruction
#if 0  
  // push_ss((void*) (builtin_sp() - 8) );
  Value * SPVal = fastBuilder.CreateCall(getSP);
  Value * SPValInt = fastBuilder.CreateCast(Instruction::PtrToInt, SPVal, IntegerType::getInt64Ty(C));
  Value * ppRA  = fastBuilder.CreateSub(SPValInt, OneByte);
  ppRA = fastBuilder.CreateCast(Instruction::IntToPtr, ppRA, IntegerType::getInt8Ty(C)->getPointerTo());
  fastBuilder.CreateCall(PUSH_SS, {ppRA});
  fastBuilder.CreateCall(potentialJump, {BlockAddress::get( unwindPathEntry )});
#endif 
        
  for( Instruction &II : *detachBB){
    if(isa<CallInst>(&II) && dyn_cast<CallInst>(&II)->getCalledFunction()->hasFnAttribute(Attribute::Forkable) ){
      // Associate callsite instruction with steal handler
      M->CallStealMap[&II].stealHandler = slowPathPrologue;
      // Associate callsite instruction with unwind handler
      M->CallStealMap[&II].unwindHandler = unwindPathEntry;
      // Indicate the steal hander basic block needs a label
      M->StealHandlerExists[M->CallStealMap[&II].stealHandler] = true;                    
      break;
    }
  }
  
  // Add the pop_ss instruction
#if 0
  bbList.clear();
  haveVisited.clear();
  // Look for the reattach inst
  // Add an epilogue just before it (POP_SS)
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
      fastBuilder.CreateCall(POP_SS);
    } else {
      for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
	bbList.push_back(*SI);
      }
    }
  }
#endif

}

Function* UNWINDABI::createDetach(DetachInst &Detach,
				  ValueToValueMapTy &DetachCtxToStackFrame,
				  DominatorTree &DT, AssumptionCache &AC, SyncInst * detachSyncPair) {

  outs() << "I am in create Detach\n";
  Detach.dump();
  outs() << "---------------------\n";

  // Find live Instruction after 
  findLiveInstAfterSync(DT, Detach, detachSyncPair);

  // GotStolen Handler
  BasicBlock * gotstolenHandler = createGotStolenHandler(Detach, detachSyncPair);

  // Temporary solution
  BasicBlock * continuation = createSlowPathFcn(Detach);

  // Create the Fast Path
  createFastPath(Detach);
  
  // Create initialization for jump table
  createJumpTableInit(Detach, gotstolenHandler);  
  // Create sort of a jump table
  createJumpTable(Detach, continuation);  
    
  encodedPcCntr++;

  // Replace the detach with a branch to the detached block.
  
  //BranchInst *DetachBr = BranchInst::Create(Detach.getDetached());
  //ReplaceInstWithInst(&Detach, DetachBr);

  return NULL;
}

void UNWINDABI::findLiveInstAfterSync(DominatorTree &DT, DetachInst &Detach, SyncInst* Sync) {  
  SmallVector<BasicBlock*, 8> bbList;
  SmallVector<BasicBlock*, 8> bbParallelRegion;
  DenseMap<BasicBlock *, bool> haveVisited;  
  BasicBlock * detachBB = Detach.getDetached();        
  BasicBlock * continueBB = Detach.getContinue();

  bbList.clear();
  haveVisited.clear();
  
  BasicBlock* bb;
  bbList.push_back(detachBB);
  while(!bbList.empty()){
    bb = bbList.back();
    bbList.pop_back();
    if ( (haveVisited.lookup(bb)) ){
      continue;
    }
    haveVisited[bb] = true;
    
    bbParallelRegion.push_back(bb);
    
    if ( isa<DetachInst>( bb->getTerminator()) || 
	 isa<SyncInst>( bb->getTerminator()) ) {      
      continue;
    } else {
      for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
	bbList.push_back(*SI);
      }
    }
  }
  
  
  
  contListV.push_back(Detach.getContinue());


  // Find the live variables
  for(auto pBB : bbParallelRegion) {
    for( Instruction &II : *pBB ) {
      outs() << "This instruciton : \n";
      II.dump();

      outs() << "Use : \n";
      for (User *U : II.users()) {
	U->dump();
	if(DT.dominates(dyn_cast<Instruction>(Sync), dyn_cast<Instruction>(U)) ){
	  outs() << "Outlive Sync inst\n";
	  II.dump();	  
	  liveAfterSyncV.push_back(&II);
	  mapInstToSyncM[&II] = Sync;
	  break;
	}
      }
    }
  }
  outs() << "------------------------\n";
}

void UNWINDABI::createJumpTableInit(DetachInst &Detach, BasicBlock * GotStolenHandler) {  
  IRBuilder<> B(unwindJumpTableInit->getTerminator());
  
  BasicBlock* BB = Detach.getParent();
  Function * F = BB->getParent();
  Module* M = F->getParent();
  LLVMContext& C = M->getContext();

  Type* Int32Ty = TypeBuilder<int32_t, false>::get(C);
  Value *ONE = ConstantInt::get(Int32Ty, 1, /*isSigned=*/false);  
  
  GlobalVariable* gUnwindStackCnt = GetGlobalVariable("unwindStackCnt", TypeBuilder<int, false>::get(C), *M, true);
  GlobalVariable* gThreadId = GetGlobalVariable("threadId", TypeBuilder<int, false>::get(C), *M, true); 
  GlobalVariable* gPrevRa = GetGlobalVariable("prevRa", TypeBuilder<addr_ty*, false>::get(C), *M, true);

  Value * ra = B.CreateLoad(gPrevRa);
  Value * detachBB = BlockAddress::get(Detach.getDetached());
  Value * contBB = BlockAddress::get(Detach.getContinue());
  
  Value * rai = B.CreateCast(Instruction::PtrToInt, ra, IntegerType::getInt64Ty(C));
  Value * detachBBi = B.CreateCast(Instruction::PtrToInt, detachBB, IntegerType::getInt64Ty(C));
  Value * contBBi = B.CreateCast(Instruction::PtrToInt, contBB, IntegerType::getInt64Ty(C));
  
  BasicBlock* workExistsBB = BasicBlock::Create(C, "work.exists", F);   
  BasicBlock* workExistsBB2 = BasicBlock::Create(C, "work.exists.two", F);   

  /*
    if (return_address >= Detach.getDetached() && return_address <= Detach.getContinue() ) {
      encoded_pc = workCtr;
      gotstolen_ra = GotStolenHandler;           
    }
  */

  Instruction* isEqOne1 = dyn_cast<Instruction>(B.CreateICmpULE(rai, contBBi));
  
  BasicBlock* afterBB = unwindJumpTableInit->splitBasicBlock(isEqOne1->getNextNode());
  
  outs() << "Get terminator\n";
  unwindJumpTableInit->getTerminator()->dump();

  auto branch = BranchInst::Create(workExistsBB, afterBB, isEqOne1);
  auto terminator = unwindJumpTableInit->getTerminator();    
  ReplaceInstWithInst(terminator, branch);  
  
  //unwindJumpTableInit->dump();

  B.SetInsertPoint(workExistsBB);
  // Dummy instruction, will be replaced
  B.CreateBr(afterBB);
  //B.CreateBr(slowPathPrologue);
  B.SetInsertPoint(workExistsBB->getTerminator());  
    
  unwindJumpTableInit = afterBB;
  
  Instruction* isEqOne2 = dyn_cast<Instruction>(B.CreateICmpUGE(rai, detachBBi));
  //workExistsBB->dump();
  afterBB = workExistsBB->splitBasicBlock(isEqOne2->getNextNode());
  branch = BranchInst::Create(workExistsBB2, afterBB, isEqOne2);
  terminator = workExistsBB->getTerminator();    
  ReplaceInstWithInst(terminator, branch);

  B.SetInsertPoint(workExistsBB2);
  
  Value * gThreadIdVal = B.CreateLoad(gThreadId);
  Value * gUnwindStackCntVal = B.CreateLoad(gUnwindStackCnt);           
  
  // TODO This
  /*
      ctx = work_deque[threadId][unwindcntr];
      unwindcntr++;          

      // Save the context similar to setjmp/longjmp
      if(mysetjmp_callee(ctx)) {
        // Push to work queue
        //enque_savecontext(ctx, threadId, joincntr);
        work_cntr[threadId][unwindcntr].joincntr = 2;
	work_owner[threadId][unwindcntr].owner = threadId;
	//work_deque[threadId][unwindcntr].loc = unwindcntr - 1;

	goto return_here;

      } else {
        work_stolen = %rdi or from the stack;
        goto slow_path_prologue;
      }
   */

  Value * pccntr = ConstantInt::get(Int32Ty, encodedPcCntr, /*isSigned=*/false);
  B.CreateStore( pccntr, encodedPc);

  //TODO : store gotstolen handler

  GlobalVariable* gWorkContext = GetGlobalVariable("workctx_arr", 
						   TypeBuilder<workcontext_ty,false>::get(C)->getPointerTo()->getPointerTo(), *M);
   
  Value* workCtxLoad = B.CreateLoad(gWorkContext);
  Value* idx2 = B.CreateInBoundsGEP(workCtxLoad, gThreadIdVal);
  Value* loadIdx2 = B.CreateLoad(idx2 );
  Value* idx1 = B.CreateInBoundsGEP(loadIdx2, gUnwindStackCntVal);
  Value* loadIdx1bitcast = B.CreateConstInBoundsGEP2_64(idx1, 0, 0);
  
  Constant* MYSETJMP_CALLEE = UNWINDRTS_FUNC(mysetjmp_callee, *M);
  
  B.CreateStore(B.CreateAdd(gUnwindStackCntVal, ONE), gUnwindStackCnt);

  Value* result = B.CreateCall(MYSETJMP_CALLEE, {loadIdx1bitcast});    
  dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);      
  
  BasicBlock *ThiefEntry            = BasicBlock::Create(C, "unwind.thief.entry", F);
  BasicBlock *AttemptUnwinding      = BasicBlock::Create(C, "unwind.attempt.unwinding", F);
  
  Value* isEqOne = B.CreateICmpEQ(result, ONE);        
  B.CreateCondBr(isEqOne, ThiefEntry, AttemptUnwinding);

  B.SetInsertPoint(ThiefEntry);
  B.CreateBr(slowPathPrologue);
  DT->insertEdge(ThiefEntry, slowPathPrologue);

  B.SetInsertPoint(AttemptUnwinding);
  B.CreateBr(returnInUnwind);

  llvm::InlineFunctionInfo ifi;
  llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);
  
  //unwindJumpTableInit = afterBB;
  //B.SetInsertPoint(unwindJumpTableInit);
  //B.CreateUnreachable();
}

void UNWINDABI::createJumpTable(DetachInst &Detach, BasicBlock * Continuation) {
  Module* M = Continuation->getModule();
  LLVMContext& Ctx = M->getContext();
  Type* Int32Ty = TypeBuilder<int32_t, false>::get(Ctx);  

  IRBuilder<> B(unwindJumpTable);  
  if(!unwindJumpTable->getTerminator()){
    B.CreateUnreachable(); 
  }  
  B.SetInsertPoint(unwindJumpTable->getTerminator());
  
  unwindJumpTable->dump();  

  Value * pccntr = ConstantInt::get(Int32Ty, encodedPcCntr, /*isSigned=*/false);
  Value * pc = B.CreateLoad(encodedPc);

  /*
    if(encoded_pc == workCtr) {
    goto Continuation;
    }
  */

  Instruction* isEqOne = dyn_cast<Instruction>(B.CreateICmpEQ(pc, pccntr));
  BasicBlock* afterBB = unwindJumpTable->splitBasicBlock(isEqOne->getNextNode()); 

  auto branch = BranchInst::Create(Continuation, afterBB, isEqOne);
  auto terminator = unwindJumpTable->getTerminator();    
  ReplaceInstWithInst(terminator, branch);
  
  unwindJumpTable = afterBB;
}

void UNWINDABI::createRestorePath(Function& F, SyncInst * SI) {
  //IRBuilder <> B(restorePath);    

  // Restore path
  //B.CreateBr(SI->getSuccessor(0));

}

#if 0
void UNWINDABI::createUnwindHandler(Function& F) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
    
  BasicBlock* unwindSaveCtx = BasicBlock::Create(C, "unwind.save.ctx", &F);      
  IRBuilder<> B(unwindPathEntry);
      
  Value* ONE = B.getInt32(1);
  Value* ZERO = B.getInt32(0);

  GlobalVariable* gSeed_ptr = GetGlobalVariable("seed_ptr", TypeBuilder<addr_ty*, false>::get(C), *M, true); 
  GlobalVariable* gThreadId = GetGlobalVariable("threadId", TypeBuilder<int, false>::get(C), *M, true); 
  GlobalVariable* gSeed_bp = GetGlobalVariable("seed_bp", TypeBuilder<addr_ty**, false>::get(C), *M);       
  GlobalVariable* gWorkContext = GetGlobalVariable("workctx_arr", 
						   TypeBuilder<workcontext_ty,false>::get(C)->getPointerTo()->getPointerTo(), *M);
   
  ///    unsigned ptr = (seed_ptr - seed_bp[threadId]);      
  Value* gThreadIdVal = B.CreateLoad(gThreadId);
  Value* gSeed_bpVal = B.CreateLoad(gSeed_bp);        
  Value* bp_location = B.CreateInBoundsGEP(gSeed_bpVal, gThreadIdVal); 
  Value* gSeed_bpEntry = B.CreateLoad(bp_location);    
  
  Value* gSeed_ptrVal = B.CreateLoad(gSeed_ptr);      
  Value* seedOffset = B.CreatePtrDiff(gSeed_ptrVal, gSeed_bpEntry);

  Value* workCtxLoad = B.CreateLoad(gWorkContext);
  Value* idx2 = B.CreateInBoundsGEP(workCtxLoad, gThreadIdVal);
  Value* loadIdx2 = B.CreateLoad(idx2 );
  Value* idx1 = B.CreateInBoundsGEP(loadIdx2, seedOffset);
  Value* loadIdx1bitcast = B.CreateConstInBoundsGEP2_64(idx1, 0, 0);
    
  Value* savedPc = B.CreateConstGEP1_32(loadIdx1bitcast, 1);   
  B.CreateStore(BlockAddress::get(slowPathPrologue), savedPc);    
  
  Constant* SAVECONTEXT = UNWINDRTS_FUNC(savecontext, *M);
  Value* result = B.CreateCall(SAVECONTEXT, {loadIdx1bitcast});        
    
  Value* isEqOne = B.CreateICmpEQ(result, ONE);
  B.CreateCondBr(isEqOne, slowPathPrologue, unwindSaveCtx);

  B.SetInsertPoint(unwindSaveCtx);

  if(F.getReturnType()->isVoidTy())
    B.CreateRetVoid();
  else if (F.getReturnType()->isIntegerTy())
    B.CreateRet(ZERO);
  else
    assert(0 && "Return type not supported yet");

  M->StealHandlerExists[unwindPathEntry] = true;

  // TODO : Inline be move to the Post Processing, when everything is complete 
  llvm::InlineFunctionInfo ifi;
  llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);
}
#else

void UNWINDABI::createUnwindHandler(Function& F) {
  Module* M = F.getParent();
  const DataLayout &DL = M->getDataLayout();
  LLVMContext& C = M->getContext();
    
  //BasicBlock* unwindSaveCtx = BasicBlock::Create(C, "unwind.save.ctx", &F);      
  IRBuilder<> B(unwindPathEntry);
      
  Value* ONE = B.getInt32(1);
  Value* ZERO = B.getInt32(0);
  Value* ZERO64 = B.getInt64(0);
  Value* OneByte = ConstantInt::get(IntegerType::getInt64Ty(C), 8, false);

  Type* Int32Ty = TypeBuilder<int32_t, false>::get(C);

  // May need to optimize it later
  GlobalVariable* gUnwindStackCnt = GetGlobalVariable("unwindStackCnt", TypeBuilder<int, false>::get(C), *M, true);
  GlobalVariable* gThreadId = GetGlobalVariable("threadId", TypeBuilder<int, false>::get(C), *M, true); 
  GlobalVariable* gPrevRa = GetGlobalVariable("prevRa", TypeBuilder<int64_t, false>::get(C), *M, true);
    
  Function* getSP = Intrinsic::getDeclaration(M, Intrinsic::x86_read_sp);
  Function* getFrameSize = Intrinsic::getDeclaration(M, Intrinsic::x86_get_frame_size);
  
  Value * gThreadIdVal = B.CreateLoad(gThreadId);
  Value * gUnwindStackCntVal = B.CreateLoad(gUnwindStackCnt);        
  Value * childRa = B.CreateLoad(gPrevRa);

  // TODO: Fix this, return address of child is modified, need to get it form heap instead of builtin_sp - 8
  // ra = *( ((void*) (builtin_sp() - 8)) );
  Value * SPVal = B.CreateCall(getSP);
  Value * SPValInt = B.CreateCast(Instruction::PtrToInt, SPVal, IntegerType::getInt64Ty(C));
  Value * ppChildRA  = B.CreateSub(SPValInt, OneByte);
  ppChildRA = B.CreateCast(Instruction::IntToPtr, ppChildRA, IntegerType::getInt64Ty(C)->getPointerTo());
  //Value * childRa = B.CreateLoad(ppChildRA);  
  
  // bp = sp + frame_size
  // parent_bp = *bp;  
  Value * FrameSizeVal = B.CreateCall(getFrameSize);
  Value * BPValInt = B.CreateAdd(SPVal, FrameSizeVal);
  BPValInt = B.CreateSub(BPValInt, OneByte);
  Value * BPVal = B.CreateCast(Instruction::IntToPtr, BPValInt, IntegerType::getInt64Ty(C)->getPointerTo());
  Value * parentBPVal = B.CreateLoad(BPVal);
  
  //parentBPVal->getType()->dump();
  Value * parentBPValInt = B.CreateCast(Instruction::PtrToInt, parentBPVal, IntegerType::getInt64Ty(C));
  // p_parent_unwind = (void*) (parent_bp-8);  
  Value * ppParentUnwind  = B.CreateSub(parentBPValInt, OneByte);
  ppParentUnwind = B.CreateCast(Instruction::IntToPtr, ppParentUnwind, IntegerType::getInt64Ty(C)->getPointerTo());
  //Value * parentUnwind = B.CreateLoad(ppParentUnwind);  
  // p_myreturnaddr = (void*) (bp+8);
  Value * ppMyRA  = B.CreateAdd(BPValInt, OneByte);
  ppMyRA = B.CreateCast(Instruction::IntToPtr, ppMyRA, IntegerType::getInt64Ty(C)->getPointerTo());
 
  
  BasicBlock* firstTimeUnwind = BasicBlock::Create(C, "first.time.unwind", &F);      
  BasicBlock* unwindBody = BasicBlock::Create(C, "unwind.body", &F);      
  // if (unwindStackCnt == 0)
  Value* isEqZero = B.CreateICmpEQ(gUnwindStackCntVal, ZERO);
  B.CreateCondBr(isEqZero, firstTimeUnwind, unwindBody);
  
  B.SetInsertPoint(firstTimeUnwind);  
  
  // if (parent_bp == 0) 
  BasicBlock* resumeInterruptedBB_1 = BasicBlock::Create(C, "resume.interrupted.one", &F);     
  BasicBlock* checkIfParentHaveBeenUnwind = BasicBlock::Create(C, "check.if.parent.unwind", &F);      
  BasicBlock* returnToUnwind_1 = BasicBlock::Create(C, "return.to.unwind.one", &F);      
  Value* isEqZero64 = B.CreateICmpEQ(parentBPValInt, ZERO64);
  B.CreateCondBr(isEqZero64, resumeInterruptedBB_1, checkIfParentHaveBeenUnwind);
  
  // if (*p_parent_unwind == 0) 
  B.SetInsertPoint(checkIfParentHaveBeenUnwind);
  Value * parentUnwindVal = B.CreateLoad(ppParentUnwind);  
  Value * parentUnwindValInt = B.CreateCast(Instruction::PtrToInt, parentUnwindVal, IntegerType::getInt64Ty(C));
  isEqZero64 = B.CreateICmpEQ(parentUnwindValInt, ZERO64);
  B.CreateCondBr(isEqZero64, resumeInterruptedBB_1, returnToUnwind_1);

  // mylongjmp_callee(resumectx);
  B.SetInsertPoint(resumeInterruptedBB_1);
  GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", TypeBuilder<workcontext_ty,false>::get(C), *M, true);
  Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );
  
  Constant* MYLONGJMP_CALLEE = UNWINDRTS_FUNC(mylongjmp_callee, *M);
  Value * result = B.CreateCall(MYLONGJMP_CALLEE, {gunwind_ctx});
  dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);
  llvm::InlineFunctionInfo ifi;
  llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);
  B.CreateBr(returnToUnwind_1);
  
  // *p_myreturnaddr = *p_parent_unwind;
  // unwindcntr++;  
  B.SetInsertPoint(returnToUnwind_1);

  B.CreateStore(B.CreateLoad(ppMyRA), gPrevRa);

  B.CreateStore(B.CreateLoad(ppParentUnwind), ppMyRA);  
  B.CreateStore(B.CreateAdd(gUnwindStackCntVal, ONE), gUnwindStackCnt);

  // return 0;
  if(F.getReturnType()->isVoidTy())
    B.CreateRetVoid();
  else if (F.getReturnType()->isIntegerTy())
    B.CreateRet(ZERO);
  else
    assert(0 && "Return type not supported yet");

  B.SetInsertPoint(unwindBody);
  // Change the child return address to default

  B.CreateStore(childRa, ppChildRA);  

  // int joincntr = 2;
  joinCntr = B.CreateAlloca(Int32Ty, DL.getAllocaAddrSpace(), nullptr, "joincntr");
  Value * nChildIR = ConstantInt::get(Int32Ty, 2, /*isSigned=*/false);
  B.CreateStore(nChildIR,  joinCntr);
  
  // int encodedPc = 0;
  encodedPc = B.CreateAlloca(Int32Ty, DL.getAllocaAddrSpace(), nullptr, "encodedPc");   
  B.CreateStore(ZERO,  encodedPc);
  B.CreateBr(unwindJumpTableInit);

  B.SetInsertPoint(unwindJumpTableInit);  

  returnInUnwind = BasicBlock::Create(C, "return.in.unwind", &F);
  B.CreateBr(returnInUnwind);

  B.SetInsertPoint(returnInUnwind);  
  BasicBlock* resumeInterruptedBB_2 = BasicBlock::Create(C, "resume.interrupted.two", &F);       
  BasicBlock* returnToUnwind_2 = BasicBlock::Create(C, "return.to.unwind.two", &F);      

  // if (*p_parent_unwind == 0)
  parentUnwindVal = B.CreateLoad(ppParentUnwind);  
  parentUnwindValInt = B.CreateCast(Instruction::PtrToInt, parentUnwindVal, IntegerType::getInt64Ty(C));
  isEqZero64 = B.CreateICmpEQ(parentUnwindValInt, ZERO64);
  B.CreateCondBr(isEqZero64, resumeInterruptedBB_2, returnToUnwind_2);
  
  B.SetInsertPoint(resumeInterruptedBB_2);
  // TODO:
  // if(unwindcntr>1) {
  //    // There is work 
  //    wordeque_ptr.tail = 1;
  //    wordeque_ptr.head = unwindcntr;
  // } else {
  //    wordeque_ptr.tail = 0;
  //    wordeque_ptr.head = 0;
  // }


  B.CreateStore(ZERO, gUnwindStackCnt);

  gUnwindContext = GetGlobalVariable("unwindCtx", TypeBuilder<workcontext_ty,false>::get(C), *M, true);
  gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );
  result = B.CreateCall(MYLONGJMP_CALLEE, {gunwind_ctx});
  dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);
  //llvm::InlineFunctionInfo ifi;
  llvm::InlineFunction(dyn_cast<CallInst>(result), ifi, nullptr, true);
  B.CreateBr(returnToUnwind_2);
  
  B.SetInsertPoint(returnToUnwind_2);
  // *p_myreturnaddr = *p_parent_unwind;  
  B.CreateStore(B.CreateLoad(ppMyRA), gPrevRa);
  B.CreateStore(B.CreateLoad(ppParentUnwind), ppMyRA);  
  
  // return 0;
  if(F.getReturnType()->isVoidTy())
    B.CreateRetVoid();
  else if (F.getReturnType()->isIntegerTy())
    B.CreateRet(ZERO);
  else
    assert(0 && "Return type not supported yet");
}
#endif

void UNWINDABI::instrumentMainFcn(Function& F) {
  // Initialize the PRSC at the beginning of main
  Module* M = F.getParent();
  IRBuilder<> B(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

  Constant* INITWORKERS_ENV = Get_initworkers_env(*M);
  Constant* DEINITWORKERS_ENV = Get_deinitworkers_env(*M);
  Constant* INITPERWORKERS_SYNC = Get_initperworkers_sync(*M);
  Constant* DEINITPERWORKERS_SYNC = Get_deinitperworkers_sync(*M);

  Value* ONE = B.getInt32(1);
  Value* ZERO = B.getInt32(0);

  // Get debug info
  //B.SetCurrentDebugLocation(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime()->getDebugLoc());

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

void UNWINDABI::instrumentSpawningFcn(Function& F) {
  Module* M = F.getParent();
  LLVMContext &Ctx = M->getContext();
  IRBuilder<> B(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

  Value *ONE = B.getInt32(1);
  Value *ZERO = B.getInt32(0);

  Constant* UNWIND_POLL = UNWINDRTS_FUNC(unwind_poll, *M);    

  // Get debug info
  //B.SetCurrentDebugLocation(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime()->getDebugLoc());

  Value* res = B.CreateCall(UNWIND_POLL);    
  Instruction* isEqOne = dyn_cast<Instruction>(B.CreateICmpEQ(res, ONE));
  BasicBlock *returnToUnwindBB = BasicBlock::Create(Ctx, "returnto.unwind", &F);
  
  // Insert basic block in middle of a basic block
  BasicBlock* afterBB = F.getEntryBlock().splitBasicBlock(isEqOne->getNextNode());
  auto branch = BranchInst::Create(returnToUnwindBB, afterBB, isEqOne);
    
  auto terminator = F.getEntryBlock().getTerminator();    
  ReplaceInstWithInst(terminator, branch);

  llvm::InlineFunctionInfo ifi;
  llvm::InlineFunction(dyn_cast<CallInst>(res), ifi, nullptr, true);
    
  B.SetInsertPoint(returnToUnwindBB);
  GlobalVariable *gUnwindContext = GetGlobalVariable("unwindCtx", TypeBuilder<workcontext_ty,false>::get(Ctx), *M, true);
  Value *gunwind_ctx = B.CreateConstInBoundsGEP2_64(gUnwindContext, 0, 0 );
  Value* savedPc = B.CreateConstGEP1_32(gunwind_ctx, 1);   
  B.CreateStore(BlockAddress::get(afterBB), savedPc);     
  if(F.getReturnType()->isVoidTy())
    B.CreateRetVoid();
  else if (F.getReturnType()->isIntegerTy())
    B.CreateRet(ZERO);
  else
    assert(0 && "Return type not supported yet");
    
  for (auto &BB : F){
    Instruction * termInst = BB.getTerminator();
    if(isa<ReturnInst>(termInst)){            
      B.SetInsertPoint(termInst);
      Value* res = B.CreateCall(UNWIND_POLL);

      Instruction* isEqOne = dyn_cast<Instruction>(B.CreateICmpEQ(res, ONE));
      BasicBlock *returnToUnwindBB = BasicBlock::Create(Ctx, "returnto.unwind2", &F);

      BasicBlock* afterBB = BB.splitBasicBlock(isEqOne->getNextNode());
      auto branch = BranchInst::Create(returnToUnwindBB, afterBB, isEqOne);
    
      auto terminator = BB.getTerminator();    
      ReplaceInstWithInst(terminator, branch);
    
      llvm::InlineFunctionInfo ifi;
      llvm::InlineFunction(dyn_cast<CallInst>(res), ifi, nullptr, true);
    

      B.SetInsertPoint(returnToUnwindBB);
      Value* savedPc = B.CreateConstGEP1_32(gunwind_ctx, 1);   
      B.CreateStore(BlockAddress::get(afterBB), savedPc);    
  
            
      if(F.getReturnType()->isVoidTy())
	B.CreateRetVoid();
      else if (F.getReturnType()->isIntegerTy())
	B.CreateRet(ZERO);
      else
	assert(0 && "Return type not supported yet");

      break;
    }
  }   
}

Value* UNWINDABI::createSlowPathPrologue(Function& F) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder <> B(slowPathPrologue);

  using AsmTypCallee = void** ( void );
  FunctionType *FAsmTypCallee = TypeBuilder<AsmTypCallee, false>::get(C);
  Value* Asm = InlineAsm::get(FAsmTypCallee, "movq %rdi, $0\n", "=r,~{rdi},~{dirflag},~{fpsr},~{flags}",/*sideeffects*/ true);    
  Value* workCtx = B.CreateCall(Asm);

  B.CreateBr(unwindJumpTable);

  B.SetInsertPoint(slowPathEpilogue);
  B.CreateUnreachable();

  //B.SetInsertPoint(restorePath);
  //B.CreateUnreachable();

  return workCtx;
}

void UNWINDABI::createSlowPathEpilogue(Function& F, Instruction* SI, Value* workCtx, BasicBlock* restorePath) {    
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();    
  IRBuilder <> B(SI);    
        
  Value* ONE = B.getInt32(1);
   
  Constant* MYSETJMP_CALLEE = UNWINDRTS_FUNC(mysetjmp_callee, *M);
  Value* result = B.CreateCall(MYSETJMP_CALLEE, {workCtx});
  dyn_cast<CallInst>(result)->setCallingConv(CallingConv::Fast);    
    
  Value* savedPc =  B.CreateConstGEP1_32(workCtx, 1);   
  B.CreateStore( BlockAddress::get(restorePath), savedPc);    

  Value* isEqOne = B.CreateICmpEQ(result, ONE);           
  BasicBlock* suspendPath = BasicBlock::Create(C, "suspend.path", &F);
  //B.CreateCondBr(isEqOne, restorePath, suspendPath);    
    
  llvm::InlineFunctionInfo ifi;
  llvm::InlineFunction(dyn_cast<CallInst>(result), ifi);

  B.SetInsertPoint(suspendPath);                       
  Function* resume2scheduler = dyn_cast<Function>(M->getOrInsertFunction( "resume2scheduler", TypeBuilder<void (void**) , false>::get(M->getContext())));
  B.CreateCall(resume2scheduler, {workCtx});
  B.CreateBr(restorePath);        

  BranchInst* restoreBr = BranchInst::Create(restorePath, suspendPath, isEqOne);
  //BranchInst *restoreBr = BranchInst::Create(restorePath);
  ReplaceInstWithInst(SI, restoreBr);
}

void UNWINDABI::preProcessFunction(Function &F) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  sync2bb.clear();
  contListV.clear();

  encodedPcCntr = 0;

  // Add Thread initialization and deinitialization on the main function
  // TODO : Make this optional
  if ( F.getName() == "main") {
    instrumentMainFcn(F); 
    return;
  }
  
  // --------------------------------------------------
  // Push the original basic block
  SmallVector<BasicBlock*, 8> bb2clones;
  for( auto &BB : F ) {      
    bb2clones.push_back(&BB);
  }
  
  // Determine whether it is TRE or spawn child
  isTre = isContinuationTre(F);
  
  // -------------------------------------------------
  // Add forkable attribute
  bool bContainSpawn = false;
  for (auto &BB : F){
    if (DetachInst * DI = dyn_cast<DetachInst>(BB.getTerminator())){          
      BasicBlock * detachBlock = dyn_cast<DetachInst>(DI)->getDetached();
      for( Instruction &II : *detachBlock ) {
	if( isa<CallInst>(&II)  && !isa<DbgInfoIntrinsic>(&II)) {
	  dyn_cast<CallInst>(&II)->getCalledFunction()->addFnAttr(Attribute::Forkable);               
	  bContainSpawn = true;
	}
      }
    }
  }

    // --------------------------------------------------------------
  // Clone the code if the code contains spawn  
  if(bContainSpawn) {
    //static ValueToValueMapTy VMapSlowPath; 
    DebugInfoFinder DIFinder;      
    DISubprogram *SP = F.getSubprogram();
    if (SP) {
      //assert(!MustCloneSP || ModuleLevelChanges);
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
    }
    
    // --------------------------------------------------------------
    // Remap the cloned instruction
    for(auto pBB : bb2clones) {
      BasicBlock * ClonedBB = dyn_cast<BasicBlock>(VMapSlowPath[pBB]);
      for (Instruction &II : *ClonedBB) {
	RemapInstruction(&II, VMapSlowPath, RF_IgnoreMissingLocals, nullptr, nullptr);        
      }
    }
  }

  // -------------------------------------------------------------
  // Create the path needed
  unwindPathEntry = BasicBlock::Create(C, "unwind.path.entry", &F);
  if(bContainSpawn) {
    slowPathEpilogue = BasicBlock::Create(C, "slow.path.epilogue", &F);
    slowPathPrologue = BasicBlock::Create(C, "slow.path.prologue", &F);        
    //restorePath = BasicBlock::Create(C, "restore.path", &F);
    unwindJumpTableInit = BasicBlock::Create(C, "unwind.jump.table.init", &F);
    unwindJumpTable = BasicBlock::Create(C, "unwind.jump.table", &F);

    // TODO:
    // Move to post Processing
    //createRestorePath(F, SI);
    createUnwindHandler(F);
    gworkCtx = createSlowPathPrologue(F);
    //createSlowPathEpilogue(F, workCtx);
    
  }  

  
  // -------------------------------------------------------------
  // Add potential jump to unwind path for every function
  Function* potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);

  for(auto pBB : bb2clones) {
    for ( auto &II : *pBB ) {
      if (isa<CallInst>(&II) && isNonPHIOrDbgOrLifetime(&II) ) {
	// Add a potential jump to unwind path
	II.dump();
	B.SetInsertPoint(&II);
	Instruction* inst = B.CreateCall(potentialJump, {BlockAddress::get( unwindPathEntry )});
      }
    }      
  }    

  // Insert polling in prologue and epilogue
  //instrumentSpawningFcn(F);  
  
  return;
}



void UNWINDABI::postProcessFunction(Function &F) {
  return;
}

void UNWINDABI::postProcessHelper(Function &F) {
  return;
}

bool UNWINDABILoopSpawning::processLoop() {
  return false;
}

Value *UNWINDABI::lowerGrainsizeCall(CallInst *GrainsizeCall) {
  assert(false);
  return nullptr;
}

bool UNWINDABI::isContinuationTre(Function &F) {
  bool tre = false;
  
  SmallVector< Loop *, 4 >  vectorLoop = LI->getLoopsInPreorder();
  for (auto &BB : F){
    if (DetachInst * DI = dyn_cast<DetachInst>(BB.getTerminator())){          
      BasicBlock * detachBlock = dyn_cast<DetachInst>(DI)->getDetached();
      for(auto elem: vectorLoop) {
	if(elem->contains(detachBlock)){
	  tre = true;
	}
      }
    }
  }
  
  return tre;
}

UNWINDABI::UNWINDABI() {}

