#include "llvm/InitializePasses.h"
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
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/ULI/EagerDTrans.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <iostream>

#define DEBUG_TYPE "eagerd-trans"

using namespace llvm;

// Set the size of the work context length
static cl::opt<int> WorkCtxLen(
  "eager-set-workctx-len", cl::init(WORKCTX_SIZE), cl::NotHidden,
  cl::desc("Size of work context length (default=WORKCTX_SIZE)"));

// Set the size of maximum grain size
static cl::opt<int> MaxGrainSize(
  "eager-set-maxgrainsize", cl::init(128), cl::NotHidden,
  cl::desc("Maximum grain size for parallel for"));

// Polling at prologue, epilogue, and inner loop
static cl::opt<int> EnableProperPolling(
"eager-enable-proper-polling", cl::init(0), cl::NotHidden,
  cl::desc("Enable polling at prologue, epilogue, and inner loop (default = 0)"));

// Instrument main function
static cl::opt<bool> EnableMainInstrumentation(
"eager-enable-main-instrumentation", cl::init(true), cl::NotHidden,
  cl::desc("Use to enable main function instrumentation automatically (default = on)"));

// Use builtin to save restore context
static cl::opt<bool> EnableSaveRestoreCtx(
"eager-enable-saverestore-ctx", cl::init(true), cl::NotHidden,
  cl::desc("Use builtin to save restore context (default = on)"));

// Use SSAUpdater to merge back slow path to fast path
static cl::opt<bool> EnableSSAUpdateTransformation(
"eager-enable-ssaupdate-xform", cl::init(true), cl::NotHidden,
  cl::desc("Use SSAUpdater to transform the detach inst  (default = on)"));

// Use the new IR and constant to see if it is working
static cl::opt<bool> EnableMultiRetIR(
"eager-enable-multiretir", cl::init(true), cl::NotHidden,
  cl::desc("Use new ir to represent fork'ed function  (default = on)"));

// TODO: http://blog.llvm.org/2011/09/greedy-register-allocation-in-llvm-30.html

#define UNWINDRTS_FUNC(name, M) Get__unwindrts_##name(M)

//using push_workctx_ty = void (void**, int*);
static FunctionCallee Get_push_workctx(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("push_workctx", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo(), PointerType::getInt32PtrTy(Ctx)}, false));
}

//using pop_workctx_ty = void (void**, int*);
static FunctionCallee Get_pop_workctx(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("pop_workctx", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo(), PointerType::getInt32PtrTy(Ctx)}, false));
}

//using sync_eagerd_ty = char (void**, int, void*, void*);
static FunctionCallee Get_sync_eagerd(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("sync_eagerd", FunctionType::get(Type::getInt8Ty(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo(), Type::getInt32Ty(Ctx), PointerType::getInt8PtrTy(Ctx), PointerType::getInt8PtrTy(Ctx)}, false));
}

//using suspend2scheduler_ty = void (int, int);
static FunctionCallee Get_suspend2scheduler(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("suspend2scheduler", FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx),Type::getInt32Ty(Ctx)}, false));
}

//using resume2scheduler_ty = void (void**, int);
static FunctionCallee Get_resume2scheduler(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("resume2scheduler", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo(), Type::getInt32Ty(Ctx)}, false));
}

//using set_joincntr_ty = void (void**);
static FunctionCallee Get_set_joincntr(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("set_joincntr", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo()}, false));
}

//using allocate_parallelctx_ty = void** ();
static FunctionCallee Get_allocate_parallelctx(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("allocate_parallelctx", FunctionType::get(PointerType::getInt8PtrTy(Ctx)->getPointerTo(), {Type::getVoidTy(Ctx)}, false));
}

//using allocate_parallelctx2_ty = void** (void**);
static FunctionCallee Get_allocate_parallelctx2(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("allocate_parallelctx2", FunctionType::get(PointerType::getInt8PtrTy(Ctx)->getPointerTo(), {PointerType::getInt8PtrTy(Ctx)->getPointerTo()}, false));
}

//using deallocate_parallelctx_ty = void (void**);
static FunctionCallee Get_deallocate_parallelctx(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("deallocate_parallelctx", FunctionType::get(Type::getVoidTy(Ctx), {PointerType::getInt8PtrTy(Ctx)->getPointerTo()}, false));
}


//using get_head_ctx_ty = void** ();
//using postunwind_ty = void (void );
//using preunwind_steal_ty = void (void );
//using postunwind_steal_ty = void (void );
//using unwind_suspend_ty = void (void );
//using unwind_workexists_ty = int (void );
//using unwind_gosteal_ty = void (void );
//using isunwind_triggered_ty = int (void);
//using initiate_unwindstack_ty = void (void);

//using initworkers_env_ty = void (void );
static FunctionCallee Get_initworkers_env(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("initworkers_env", FunctionType::get(Type::getVoidTy(Ctx), {Type::getVoidTy(Ctx)}, false));
}

//using deinitworkers_env_ty = void (void );
static FunctionCallee Get_deinitworkers_env(Module& M) {
  LLVMContext &Ctx = M.getContext();
  return M.getOrInsertFunction("deinitworkers_env", FunctionType::get(Type::getVoidTy(Ctx), {Type::getVoidTy(Ctx)}, false));
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

#if 1
  // Create helper function
  Function* GenerateWrapperFunc(CallInst* CI, SmallPtrSet<Value*, 8> storageVec, SmallVector<Instruction *, 4>& insts2clone, Type* workCtxType) {
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

    Type *VoidTy = Type::getVoidTy(C);
    FunctionType *FTy = F.getFunctionType();
    assert(!FTy->isFunctionVarArg());
    Type *RetType = FTy->getReturnType();

    FunctionCallee PUSH_WORKCTX = Get_push_workctx(*M);
    FunctionCallee POP_WORKCTX = Get_pop_workctx(*M);

    SmallVector<Type *, 8> WrapperParamTys(FTy->param_begin(), FTy->param_end());
    WrapperParamTys.push_back(workCtxType);

    if(!RetType->isVoidTy()) {
      for(auto storage: storageVec) {
	WrapperParamTys.push_back(storage->getType());
      }
    }

    FunctionType *WrapperFTy = FunctionType::get(VoidTy, WrapperParamTys, /*isVarArg=*/false);

    Function *Wrapper = Function::Create(WrapperFTy, InternalLinkage, Name, M);
    BasicBlock *Entry = BasicBlock::Create(C, "entry", Wrapper);

    unsigned sizeOfOutput = storageVec.size();

    unsigned endIdx = 1;
    if(!RetType->isVoidTy())
      endIdx = endIdx + sizeOfOutput;

    IRBuilder<> B(Entry);
    SmallVector<Value*, 8> Args;
    for (auto it = Wrapper->arg_begin(); it < Wrapper->arg_end() - endIdx; ++it) {
      Args.push_back(it);
    }

    auto ctxArg = Wrapper->arg_end() - endIdx;
    auto pointerArg= Wrapper->arg_end() - 1;

    // Create stack variable to store the state whether work is push or not
    Value* bWorkNotPushedAlloc = B.CreateAlloca(IntegerType::getInt32Ty(M->getContext()), DL.getAllocaAddrSpace(), nullptr, "bWorkNotPushed");

    // Push the work
    auto res0 = B.CreateCall(PUSH_WORKCTX, {ctxArg, bWorkNotPushedAlloc});
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

    auto res1 = B.CreateCall(POP_WORKCTX, {ctxArg, bWorkNotPushedAlloc});
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
      if (fn->getIntrinsicID() != Intrinsic::uli_potential_jump) continue;
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
            if(fn && (fn->getIntrinsicID() == Intrinsic::var_annotation || fn->getIntrinsicID() == Intrinsic::uli_potential_jump) ) {
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

    Type *VoidTy = Type::getVoidTy(C);
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

    //errs() << "Body of the function:\n";
    for(auto pBB : bb2clones) {
      BasicBlock * ClonedBB = dyn_cast<BasicBlock>(VMapSlowPath[pBB]);
      for (Instruction &II : *ClonedBB) {
        //II.dump();
      }
    }


    return Wrapper;
  }
#endif


}


namespace llvm {
  struct EagerDTrans : public FunctionPass {
  public:
    static char ID;
    explicit EagerDTrans() : FunctionPass(ID) { initializeEagerDTransPass(*PassRegistry::getPassRegistry()); }
    // We don't modify the program, so we preserve all analyses
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      //Impl.runAnalysisUsage(AU);
      AU.addRequired<LoopInfoWrapperPass>();
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<DominanceFrontierWrapperPass>();
    }

    StringRef getPassName() const override {
      return "Simple Lowering of Tapir to EagerD ABI";
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
    EagerDTransPass Impl;
  };
}

// LLVM uses the address of this static member to identify the pass, so the
// initialization value is unimportant.
char EagerDTrans::ID = 0;

INITIALIZE_PASS_BEGIN(EagerDTrans, "EagerDTrans",
                      "Lower Tapir to EagerDTrans", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass);
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominanceFrontierWrapperPass);
INITIALIZE_PASS_END(EagerDTrans, "EagerDTrans",
                    "Lower Tapir to EagerDTrans", false, false)


/// Copied from CilkABI.cpp
/// \brief Lower a call to get the grainsize of this Tapir loop.
///
/// The grainsize is computed by the following equation:
///
///     Grainsize = min(2048, ceil(Limit / (8 * workers)))
///
/// This computation is inserted into the preheader of the loop.
Value* EagerDTransPass::lowerGrainsizeCall(CallInst *GrainsizeCall) {
  Value *Limit = GrainsizeCall->getArgOperand(0);
  Module *M = GrainsizeCall->getModule();
  IRBuilder<> Builder(GrainsizeCall);

  // Get 8 * workers
  Value *Workers = Builder.CreateCall(UNWINDRTS_FUNC(get_nworkers, *M));
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


void EagerDTransPass::replaceUses(Instruction *liveVar, Instruction *slowLiveVar) {
  SmallVector< Use*, 4 >  useNeed2Update;
  for (auto &use : slowLiveVar->uses()) {
    useNeed2Update.push_back(&use);
  }
  for( auto U : useNeed2Update ){
    U->set(liveVar);
  }
  return;
}


void EagerDTransPass::simplifyFcn(Function &F) {
  const SimplifyCFGOptions Options;
#if 0
  auto *TTI = &getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);
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


void EagerDTransPass::postProcessCfg(Function &F) {
  simplifyFcn(F);
  // Verify function
  //F.dump();
  if (verifyFunction(F, &errs())) {
    llvm_unreachable("Tapir lowering produced bad IR!");
  }
  return;
}

void EagerDTransPass::createParallelRegion(Function& F, SmallVector<DetachInst*, 4> bbOrder, DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIPath, DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB, DenseMap<SyncInst *, SmallPtrSet<BasicBlock*, 8>>& RSIPath, SmallPtrSet<BasicBlock*, 32>& parallelRegions, SmallPtrSet<BasicBlock*, 32>& frontierParallelRegions, SmallPtrSet<BasicBlock*, 32>& exitParallelRegions) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  // Create the parallel region by unioning the result of RDI and RSI Path
  for (auto DI: bbOrder) {
    auto reachingBBs = RDIPath[DI];
    for(auto reachingBB: reachingBBs) {
      if(reachingBB)
	parallelRegions.insert(reachingBB);
    }
  }
  for(auto elem: RSIPath) {
    auto reachingBBs = elem.second;
    for(auto reachingBB: reachingBBs) {
      if(reachingBB)
	parallelRegions.insert(reachingBB);
    }
  }

  for(auto parallelBB : parallelRegions) {
    LLVM_DEBUG(dbgs() << "Parallel bb: " << parallelBB->getName() << "\n");
  }

  //SmallPtrSet<BasicBlock*, 32> frontierParallelRegions;
  // Find basic block that are outside the parallel region
  for(auto& bb : F) {
    if (parallelRegions.find(&bb) == parallelRegions.end()){
      for ( succ_iterator SI = succ_begin(&bb); SI != succ_end(&bb); SI++ ) {
	auto succBB = *SI;
	if (parallelRegions.find(succBB) != parallelRegions.end()) {
	  frontierParallelRegions.insert(&bb);
	}
      }
    }
  }

  for(auto frontierParallelBB : frontierParallelRegions) {
    LLVM_DEBUG(dbgs() << "Frontier Parallel BB: " << frontierParallelBB->getName() << "\n");
  }

  for (auto bb : parallelRegions){
    for ( succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++ ) {
      auto succBB = *SI;
      if (parallelRegions.find(succBB) == parallelRegions.end()) {
	exitParallelRegions.insert(succBB);
      }
    }
  }

  // Look for block that is the exit of the parallel region
  for(auto exitParallelBB : exitParallelRegions) {
    LLVM_DEBUG(dbgs() << "Exit Parallel BB: " << exitParallelBB->getName() << "\n");
  }

  return;
}

void EagerDTransPass::initializeParallelCtx(Function& F, SmallVector<DetachInst*, 4> bbOrder, DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIPath, DenseMap<DetachInst *, SmallPtrSet<BasicBlock*, 8>>& RDIBB, Value* readyctx, Value* ownerAlloc, SmallPtrSet<BasicBlock*, 32>& parallelRegions, SmallPtrSet<BasicBlock*, 32>& frontierParallelRegions){
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  Type* VoidPtrTy = PointerType::getInt8PtrTy(C);
  Type* Int32Ty = IntegerType::getInt32Ty(C);

  // For basic block not part of parallel region that will imm. enter it, initialize ctx before entering it.
  for(auto frontierParallelBB: frontierParallelRegions) {
    // TODO: Create critical edge (or create preentry to parallel region)
    // Initialize context there, and jump to the parallel region


    auto brTerminator = (frontierParallelBB->getTerminator());

    if(isa<DetachInst>(brTerminator)) {
      B.SetInsertPoint(brTerminator);
#if 1
      FunctionCallee allocate_parallelctx2 = Get_allocate_parallelctx2(*M);
      B.CreateCall(allocate_parallelctx2, {readyctx});
#endif
      // Get rsp
      auto* getSP = Intrinsic::getDeclaration(M, Intrinsic::read_sp);
      Value* spval = B.CreateCall(getSP);
      // Store resp to the readyctxAlloc
      auto savedSP = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_RSP);
      auto spvalAsPtr = B.CreateCast(Instruction::IntToPtr, spval, IntegerType::getInt8Ty(C)->getPointerTo());
      B.CreateStore(spvalAsPtr, savedSP);

      // Debug purpose
      auto savedbStolen = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_SLOWPATH_DEQUE);
      auto zeroAsPtr = B.CreateCast(Instruction::IntToPtr, B.getInt32(0), IntegerType::getInt8Ty(C)->getPointerTo());
      B.CreateStore(zeroAsPtr, savedbStolen);

      // Debug purpose?
      Value* r8value = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_ADDRLOC); //void** (no loading involved)
      B.CreateStore(zeroAsPtr, r8value);

      // Debug purpose?
      Value* executedBy = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_EXECUTEDBY_OWNER); //void** (no loading involved)
      Value* negOneAsPointer = B.CreateCast(Instruction::IntToPtr, B.getInt32(-1), IntegerType::getInt8Ty(C)->getPointerTo());
      B.CreateStore(negOneAsPointer, executedBy);

#if 1
      auto ownerVal = B.CreateAlignedLoad(Int32Ty, ownerAlloc, Align(4));
      Value* threadIdAsPointer = B.CreateCast(Instruction::IntToPtr, ownerVal, IntegerType::getInt8Ty(C)->getPointerTo());
      Value* ownerRef = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_OWNER); //void** (no loading involved)
      B.CreateStore(threadIdAsPointer, ownerRef);
#endif
#if 1
      Value* readyctxAsPointer = B.CreateBitCast(readyctx, IntegerType::getInt8Ty(C)->getPointerTo());
      Value* readyctxRef = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_READYCTX); //void** (no loading involved)
      B.CreateStore(readyctxAsPointer, readyctxRef);
#endif
    } else {
      unsigned nSuccessors  = brTerminator->getNumSuccessors();

      for (unsigned i = 0; i < nSuccessors; i++) {
	auto succBB = brTerminator->getSuccessor(i);
	if (parallelRegions.find(succBB) == parallelRegions.end()) continue;

	BasicBlock* preParallelEntry = BasicBlock::Create(C, "pre.parallel.entry", &F);
	brTerminator->setSuccessor(i, preParallelEntry);
	B.SetInsertPoint(preParallelEntry);
#if 1
	FunctionCallee allocate_parallelctx2 = Get_allocate_parallelctx2(*M);
	B.CreateCall(allocate_parallelctx2, {readyctx});
#endif
	// Get rsp
	auto* getSP = Intrinsic::getDeclaration(M, Intrinsic::read_sp);
	Value* spval = B.CreateCall(getSP);
	// Store resp to the readyctxAlloc
	auto savedSP = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_RSP);
	auto spvalAsPtr = B.CreateCast(Instruction::IntToPtr, spval, IntegerType::getInt8Ty(C)->getPointerTo());
	B.CreateStore(spvalAsPtr, savedSP);

	// Debug purpose
	auto savedbStolen = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_SLOWPATH_DEQUE);
	auto zeroAsPtr = B.CreateCast(Instruction::IntToPtr, B.getInt32(0), IntegerType::getInt8Ty(C)->getPointerTo());
	B.CreateStore(zeroAsPtr, savedbStolen);

	// Debug purpose?
	Value* r8value = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_ADDRLOC); //void** (no loading involved)
	B.CreateStore(zeroAsPtr, r8value);

	// Debug purpose?
	Value* executedBy = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_EXECUTEDBY_OWNER); //void** (no loading involved)
	Value* negOneAsPointer = B.CreateCast(Instruction::IntToPtr, B.getInt32(-1), IntegerType::getInt8Ty(C)->getPointerTo());
	B.CreateStore(negOneAsPointer, executedBy);

#if 1
	auto ownerVal = B.CreateAlignedLoad(Int32Ty, ownerAlloc, Align(4));
	Value* threadIdAsPointer = B.CreateCast(Instruction::IntToPtr, ownerVal, IntegerType::getInt8Ty(C)->getPointerTo());
	Value* ownerRef = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_OWNER); //void** (no loading involved)
	B.CreateStore(threadIdAsPointer, ownerRef);
#endif
#if 1
	Value* readyctxAsPointer = B.CreateBitCast(readyctx, IntegerType::getInt8Ty(C)->getPointerTo());
	Value* readyctxRef = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_READYCTX); //void** (no loading involved)
	B.CreateStore(readyctxAsPointer, readyctxRef);
#endif
	B.CreateBr(succBB);

	////////////////////////////////////
	// Fix phi node
	for(auto &ii: *succBB) {
	  if(isa<PHINode>(&ii)){
	    // Change the incoming BB
	    PHINode* phiN = dyn_cast<PHINode>(&ii);
	    unsigned incomingPair = phiN->getNumIncomingValues();
	    for(unsigned i = 0; i<incomingPair; i++)  {
	      BasicBlock* incomingBB = phiN->getIncomingBlock(i);
	      if ( incomingBB == frontierParallelBB ) {
		phiN->setIncomingBlock(i, preParallelEntry);
	      }
	    }
	  }
	}
	/////////////////////////////////

      }
    }
  }
  return;
}

void EagerDTransPass::instrumentSlowPath(Function& F, SmallVector<DetachInst*, 4>& seqOrder, SmallVector<DetachInst*, 4>& loopOrder,  SmallVector<SyncInst*, 8>& syncInsts,
			Value* ownerAlloc, Value* joincntrAlloc, Value* readyctx){

  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  Type* Int32Ty = IntegerType::getInt32Ty(C);
  Type* VoidPtrTy = PointerType::getInt8PtrTy(C);

  // workctx contains information related to running the parallel task, such as join counter callee register, etc.

  // Loop through the detach basic block that corresponds to the slow path
  for (auto di : bbOrder) {
    auto pBB = di->getParent();
    LLVM_DEBUG(dbgs() << "Processing detach: " << *di << "\n");
    assert(pBB);
    // No need to get detach from slow path instr
    auto diSlowPath = dyn_cast<DetachInst>(di);
    auto pBBSlowPath = diSlowPath->getParent();
    assert(diSlowPath && "Detach basic block should not have been modified, invariant not met");

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

    // Get the workctx
#if 0
    FunctionCallee GetHeadCtxFcnCall = Get_get_head_ctx(*M);
    Value* workCtx = B.CreateCall(GetHeadCtxFcnCall);
    workCtx->getType()->dump();
#endif

    //Value* readyctx = B.CreateConstInBoundsGEP2_64(readyctxAlloc, 0, 0 );
    Value* workCtx = readyctx;

    // Save owner, join counter location, and ready context location
    //Value* pJoinctr = B.CreateBitCast(joincntrAlloc, IntegerType::getInt8Ty(C)->getPointerTo());
    //Value* joinCtrRef = B.CreateConstGEP1_32(workCtx, I_JOINCNT); //void** (no loading involved)
    //B.CreateStore(pJoinctr, joinCtrRef);

#if 0
    auto ownerVal = B.CreateAlignedLoad(Int32Ty, ownerAlloc,Align(4));
    Value* threadIdAsPointer = B.CreateCast(Instruction::IntToPtr, ownerVal, IntegerType::getInt8Ty(C)->getPointerTo());
    Value* ownerRef = B.CreateConstGEP1_32(VoidPtrTy, workCtx, I_OWNER); //void** (no loading involved)
    B.CreateStore(threadIdAsPointer, ownerRef);
#endif

#if 0

    Value* readyctxAsPointer = B.CreateBitCast(readyctx, IntegerType::getInt8Ty(C)->getPointerTo());
    Value* readyctxRef = B.CreateConstGEP1_32(VoidPtrTy, workCtx, I_READYCTX); //void** (no loading involved)
    B.CreateStore(readyctxAsPointer, readyctxRef);
#endif

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
      //auto saveContextNoSP = Intrinsic::getDeclaration(M, Intrinsic::uli_save_callee_nosp);
      auto saveContextNoSP = Intrinsic::getDeclaration(M, Intrinsic::uli_save_context_nosp);

      //B.CreateCall(saveContextNoSP, {B.CreateBitCast(workCtx, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});

      BasicBlock* preDetachSlowPath = BasicBlock::Create(C, "pre.detachSlowpath", &F);
      BasicBlock* preContinueSlowPath = BasicBlock::Create(C, "pre.continueSlowpath", &F);

      //auto insertPoint = B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), detachedSlowPath, {continueSlowPath}, {});
      //auto insertPoint = B.CreateMultiRetCall(dyn_cast<Function>(saveContextNoSP), detachedSlowPath, {continueSlowPath}, {B.CreateBitCast(workCtx, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});
      auto insertPoint = B.CreateMultiRetCall(dyn_cast<Function>(saveContextNoSP), preDetachSlowPath, {preContinueSlowPath}, {B.CreateBitCast(workCtx, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});
      diSlowPath->eraseFromParent();

      B.SetInsertPoint(preDetachSlowPath);
      B.CreateRetPad(dyn_cast<MultiRetCallInst>(insertPoint));
      B.CreateBr(detachedSlowPath);

      B.SetInsertPoint(preContinueSlowPath);
      B.CreateRetPad(dyn_cast<MultiRetCallInst>(insertPoint));
      B.CreateBr(continueSlowPath);

    } else {
      assert(0 && "No longer supported");
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
    FunctionCallee PUSH_WORKCTX = Get_push_workctx(*M);
    FunctionCallee POP_WORKCTX = Get_pop_workctx(*M);
    B.SetInsertPoint(detachedSlowPath->getFirstNonPHIOrDbgOrLifetime());

    if(EnableSaveRestoreCtx) {
      Value* savedPc = B.CreateConstGEP1_32(VoidPtrTy, workCtx, 1);
      B.CreateStore(BlockAddress::get(pBBSlowPath, 1), savedPc);
    }

    bool bStartClone = false;
    SmallVector<Instruction *, 4> insts2clone;
    SmallPtrSet<Instruction *, 4> insts2cloneSet;

    //----------------------------------------------------------------------------------------------------
    // Generate wrapper function
    // Find the call inst and store inst
    CallInst* ci = nullptr;
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

    // Epilogue for the slow path
    B.SetInsertPoint(detachedSlowPath->getTerminator());

    //workCtx = B.CreateCall(GetHeadCtxFcnCall);

    Function* wrapperFcn = nullptr;
    if(!ci->getCalledFunction()->getReturnType()->isVoidTy())
      wrapperFcn = GenerateWrapperFunc(ci, storageVec, insts2clone, workCtx->getType());
    else
      wrapperFcn = GenerateWrapperFunc(ci, storageVec, insts2clone, workCtx->getType());

    wrapperFcn->addFnAttr("no-frame-pointer-elim", "true");
    wrapperFcn->addFnAttr(Attribute::NoUnwindPath);
    wrapperFcn->addFnAttr(Attribute::NoInline);
    wrapperFcn->addFnAttr(Attribute::OptimizeNone); // Can cause a ud2 in assembly?

    SmallVector<Value*, 4> args;
    for(int i = 0; i<ci->arg_size(); i++){
      args.push_back(ci->getArgOperand(i));
    }
    args.push_back(workCtx);
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
	  unsigned incomingPair = phiN->getNumIncomingValues();
	  Value * inst2copy = nullptr;
	  for(unsigned i = 0; i<incomingPair; i++)  {
	    BasicBlock* incomingBB = phiN->getIncomingBlock(i);
	    if ( incomingBB == detachedSlowPath ) {
	      inst2copy = (phiN->getIncomingValue(i));
	    }
	  }
	  if(inst2copy) {
	    phiN->addIncoming(inst2copy, pBBSlowPath);
	  }
	}
      }
    }
  }


  Value* NULL8 = ConstantPointerNull::get(IntegerType::getInt8Ty(C)->getPointerTo());
  // Get the sync instruction that corresponds to the slow path
  for(auto syncInst : syncInsts) {
    auto syncBB = syncInst->getParent();
    auto syncSlowPath = dyn_cast<SyncInst>(syncInst);
    auto syncBBSlowPath = syncSlowPath->getParent();

    //auto syncBBSlowPath = dyn_cast<BasicBlock>(VMapSlowPath[syncBB]);
    assert(syncSlowPath && "Sync inst should not have been modified, invariant not met");
    assert(syncBBSlowPath && "Sync basic block should not have been modified, invariant not met");

    BasicBlock* syncRuntimeBB = BasicBlock::Create(C, "sync.resume.to.scheduler", &F);
    BasicBlock* syncPreRuntimeBB = BasicBlock::Create(C, "sync.pre.resume.to.scheduler", &F);
    BasicBlock* syncPreResumeParentBB = BasicBlock::Create(C, "sync.pre.resume.parent", &F);
    BasicBlock* syncSucc = syncSlowPath->getSuccessor(0);

    // Get the work ctx (again)
    B.SetInsertPoint(syncSlowPath);


    //Value* readyctx = B.CreateConstInBoundsGEP2_64(readyctxAlloc, 0, 0 );
    auto savedRSP = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_RSP);
    savedRSP = B.CreateBitCast(savedRSP, IntegerType::getInt8Ty(C)->getPointerTo()->getPointerTo());

    auto* getSP = Intrinsic::getDeclaration(M, Intrinsic::read_sp);
    Value* spval = B.CreateCall(getSP);
    auto currentRSP = B.CreateCast(Instruction::IntToPtr, spval, IntegerType::getInt8Ty(C)->getPointerTo());

    // Call sync function call
    FunctionCallee sync_eagerd = Get_sync_eagerd(*M);
    auto sync_eagerd_res = B.CreateCall(sync_eagerd, {readyctx, B.CreateAlignedLoad(Int32Ty, ownerAlloc,Align(4)), B.CreateLoad(VoidPtrTy, savedRSP), currentRSP});
    auto sync_eagerd_rescmp = B.CreateICmpEQ(sync_eagerd_res, B.getInt8(1));
    B.CreateCondBr(sync_eagerd_rescmp, syncSucc, syncPreRuntimeBB);

    // If the target instruction has a phi node, from syncSlowPath, create a dataflow from syncPreRuntimeBB as well
    // Example:
    /*
      if.end18:                                         ; preds = %sync.pre.resume.to.scheduler2, %det.cont11, %sync.pre.resume.to.scheduler, %det.cont
      %b.0 = phi i32 [ %call7, %det.cont ], [ %call16, %det.cont11 ]
      %a.0.load48 = load i32, i32* %a, align 4
      %add19 = add nsw i32 %a.0.load48, %b.0
      br label %cleanup

      to

      %b.0 = phi i32 [ %call7, %det.cont ], [ %call7, %sync.pre.resumte.to.scheduler2], [ %call16, %det.cont11 ], [ %call16, %sync.pre.resume.to.scheduler]
      %a.0.load48 = load i32, i32* %a, align 4
      %add19 = add nsw i32 %a.0.load48, %b.0
      br label %cleanup

    */

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
	  phiN->addIncoming(inst2copy, syncPreResumeParentBB);
	}
      }
    }

    //Constant* GetWorkCtxFcnCall = Get_get_workcontext(*M);

    /*
      %15 = call i8** asm sideeffect "movq %rdi, $0\0A", "=r,~{rdi},~{dirflag},~{fpsr},~{flags}"()
      %16 = call i32 @mysetjmp_callee(i8** %15)
      %17 = icmp eq i32 %16, 0
      br i1 %17, label %sync.resume.to.scheduler2, label %sync.continue17.slowPath
    */

    B.SetInsertPoint(syncPreRuntimeBB);

    //readyctx = B.CreateConstInBoundsGEP2_64(readyctxAlloc, 0, 0 );

    CallInst* setjmp = nullptr;

    if(EnableSaveRestoreCtx) {
      auto donothingFcn = Intrinsic::getDeclaration(M, Intrinsic::donothing);
      //auto saveContextNoSP = Intrinsic::getDeclaration(M, Intrinsic::uli_save_callee_nosp);
      auto saveContextNoSP = Intrinsic::getDeclaration(M, Intrinsic::uli_save_context_nosp);
      CallInst* result = B.CreateCall(saveContextNoSP, {B.CreateBitCast(readyctx, IntegerType::getInt8Ty(C)->getPointerTo()), NULL8});

      B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), syncRuntimeBB, {syncPreResumeParentBB}, {});
      //B.CreateMultiRetCall(dyn_cast<Function>(donothingFcn), syncSucc, {syncSucc}, {});
      syncSlowPath->eraseFromParent();

    } else {
      assert(0 && "No longer supported");
    }

    /*
      sync.resume.to.scheduler:                         ; preds = %det.cont.slowPath
      call void @resume2scheduler(i8** %8)
      br label %sync.continue.slowPath
    */

    // Create a basic block that performs the synchronization
    B.SetInsertPoint(syncRuntimeBB);
    Value* savedPc = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_RIP); //void** (no loading involved)

    if(EnableMultiRetIR)
      B.CreateStore(BlockAddress::get(syncPreRuntimeBB, 1), savedPc);
    else
      B.CreateStore(BlockAddress::get(syncSucc), savedPc);

    Value* newsp = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_NEWRSP);
    newsp = B.CreateLoad(VoidPtrTy, newsp);

    // Save owner and join counter location
    //Value* pJoinctr = B.CreateBitCast(joincntrAlloc, IntegerType::getInt8Ty(C)->getPointerTo());
    //Value* joinCtrRef = B.CreateConstGEP1_32(readyctx, I_JOINCNT); //void** (no loading involved)
    //B.CreateStore(pJoinctr, joinCtrRef);

    auto ownerVal = B.CreateAlignedLoad(Int32Ty, ownerAlloc,Align(4));
    Value* threadIdAsPointer = B.CreateCast(Instruction::IntToPtr, ownerVal, IntegerType::getInt8Ty(C)->getPointerTo());
    Value* ownerRef = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_OWNER); //void** (no loading involved)
    B.CreateStore(threadIdAsPointer, ownerRef);

    FunctionCallee resume2scheduler = Get_resume2scheduler(*M);
    B.CreateCall(resume2scheduler, {readyctx, B.getInt32(1)});
    B.CreateUnreachable();
    //B.CreateBr(syncSucc);

    // Inline the setjmp
    if(setjmp) {
      llvm::InlineFunctionInfo ifi;
      llvm::InlineFunction(*setjmp, ifi, nullptr, true);
    }

    // When resuming parent, the join cntr is set to 1 first

    B.SetInsertPoint(syncPreResumeParentBB);
    FunctionCallee set_joincntr = Get_set_joincntr(*M);
    B.CreateCall(set_joincntr, {readyctx});
    B.CreateBr(syncSucc);

  }
  return;
}

void EagerDTransPass::deinitializeParallelCtx(Function& F, Value* joincntrAlloc, Value* readyctx, SmallPtrSet<BasicBlock*, 32>& exitParallelRegions) {
  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  IRBuilder<> B(C);

  Type* VoidPtrTy = PointerType::getInt8PtrTy(C);

  // Deinitialize at exit
  for(auto exitParallelBB : exitParallelRegions) {
    B.SetInsertPoint(exitParallelBB->getFirstNonPHIOrDbgOrLifetime());
#if 0
    // Resore the join counter
    B.CreateAlignedStore(B.getInt32(1), joincntrAlloc, Align(4), 1);
#endif

    //readyctx = B.CreateConstInBoundsGEP2_64(readyctxAlloc, 0, 0 );
    auto savedbStolen = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_SLOWPATH_DEQUE);
    auto zeroAsPtr = B.CreateCast(Instruction::IntToPtr, B.getInt32(0), IntegerType::getInt8Ty(C)->getPointerTo());
    B.CreateStore(zeroAsPtr, savedbStolen);

#if 0
    // Nothing
    alreadyResume = B.CreateConstGEP1_32(VoidPtrTy, readyctx, I_ALREADY_RESUMED);
    oneAsPtr = B.CreateCast(Instruction::IntToPtr, B.getInt32(0), IntegerType::getInt8Ty(C)->getPointerTo());
    B.CreateStore(oneAsPtr, alreadyResume);

#else
    FunctionCallee deallocate_parallelctx = Get_deallocate_parallelctx(*M);
    B.CreateCall(deallocate_parallelctx, {readyctx});
#endif
  }
  return;
}


void EagerDTransPass::instrumentMainFcn(Function& F) {
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
bool EagerDTransPass::runInitialization(Module &M) {
  return false;
}


// We don't modify the program, so we preserve all analyses
void EagerDTransPass::runAnalysisUsage(AnalysisUsage &AU) const  {
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<DominanceFrontierWrapperPass>();
}

bool EagerDTransPass::runImpl(Function &F, FunctionAnalysisManager &AM, DominatorTree &DT,  DominanceFrontier &DF, LoopInfo &LI) {

  if(F.getName() == "main") {
    outs() << "Source filename: " << F.getParent()->getSourceFileName() << "\n";
    if(EnableMainInstrumentation)
      instrumentMainFcn(F);
    F.addFnAttr(Attribute::NoUnwindPath);
  }

  LiveVariable LV;
  ReachingDetachInst RDI;
  ReachingStoreReachableLoad RSI;

  LV.recalculate(F);
  RDI.recalculate(F, AM, DT, LI);
  RSI.recalculate(F, AM, DT, LI);

  auto  &RDIPath = RDI.getReachingDetachPathMap();
  auto  &RSIPath = RDI.getReachingSyncPathMap();
  auto  &RDIBB = RDI.getReachingDetachBBMap();

  auto  &seqOrder = RDI.getSeqOrderInst();
  auto  &loopOrder = RDI.getLoopOrderInst();

  SmallVector<DetachInst*, 4> bbOrder;
  bbOrder.append(seqOrder.begin(), seqOrder.end());
  bbOrder.append(loopOrder.begin(), loopOrder.end());

  // The original basic block that needs to be cloned.
  SmallVector<BasicBlock*, 8> bb2clones;
  for( auto &BB : F ) {
    bb2clones.push_back(&BB);
  }

  SmallVector<SyncInst*, 8> syncInsts;
  for( auto pBB : bb2clones ) {
    if(isa<SyncInst>( pBB->getTerminator())) {
      syncInsts.push_back(dyn_cast<SyncInst>( pBB->getTerminator()));
    }
  }

  // qsort will generate an error without this
  if(F.getName().contains(F.getParent()->getSourceFileName())) {
    F.addFnAttr(Attribute::NoUnwindPath);
  }

  // Do not process function that have the nounwindpath attribute
  if(F.hasFnAttribute(Attribute::NoUnwindPath)) {
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

    return false;
  }


  Module* M = F.getParent();
  LLVMContext& C = M->getContext();
  const DataLayout &DL = M->getDataLayout();
  // Potential Jump Fcn
  IRBuilder<> B(C);

  Type* Int32Ty = IntegerType::getInt32Ty(C);

  // Create memory to store location of parallel task in workctx_ar
  B.SetInsertPoint(F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

  Value* ownerAlloc = B.CreateAlloca(IntegerType::getInt32Ty(M->getContext()), DL.getAllocaAddrSpace(), nullptr, "owner");
  // May not be needed
  Value* joincntrAlloc = B.CreateAlloca(IntegerType::getInt32Ty(M->getContext()), DL.getAllocaAddrSpace(), nullptr, "joincntr");


#if 1
  Value* readyctxAlloc = B.CreateAlloca(ArrayType::get(PointerType::getInt8PtrTy(C), WorkCtxLen), DL.getAllocaAddrSpace(), nullptr, "readyCtx");
  Value* readyctx = B.CreateConstInBoundsGEP2_64(PointerType::getInt8PtrTy(C)->getPointerTo(), readyctxAlloc, 0, 0 );
#else
  FunctionCallee allocate_parallelctx = Get_allocate_parallelctx(*M);
  Value* readyctx = B.CreateCall(allocate_parallelctx);
#endif
  // Initialize owner
  GlobalVariable* gThreadId = GetGlobalVariable("threadId", Type::getInt32Ty(C), *M, true);
  Value * gThreadIdVal = B.CreateAlignedLoad(Int32Ty, gThreadId, Align(4));
  B.CreateAlignedStore(gThreadIdVal, ownerAlloc, Align(4), 1);

  //-------------------------------------------------------------------------------------------------
  // Create Parallel region
  SmallPtrSet<BasicBlock*, 32> frontierParallelRegions;
  SmallPtrSet<BasicBlock*, 32> exitParallelRegions;
  SmallPtrSet<BasicBlock*, 32> parallelRegions;
  createParallelRegion(F, bbOrder, RDIPath, RDIBB, RSIPath, parallelRegions, frontierParallelRegions, exitParallelRegions);

  //-------------------------------------------------------------------------------------------------
  // Initialize the parallel ctx
  initializeParallelCtx(F, bbOrder, RDIPath, RDIBB, readyctx, ownerAlloc, parallelRegions, frontierParallelRegions);

  //-------------------------------------------------------------------------------------------------
  // Parallelize Fcn
  // Add runtime to parallelize fcn
  instrumentSlowPath(F, seqOrder, loopOrder, syncInsts, ownerAlloc, joincntrAlloc, readyctx);

  //-------------------------------------------------------------------------------------------------
  // Deinitialize outside parallel region
  deinitializeParallelCtx(F, joincntrAlloc, readyctx, exitParallelRegions);

  //-------------------------------------------------------------------------------------------------
  // Post process: Simplify CFG and verify function
  postProcessCfg(F);

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
EagerDTransPass::run(Function &F, FunctionAnalysisManager &AM) {
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

  Pass *createEagerDTransPass() {
    return new EagerDTrans();
  }

}
