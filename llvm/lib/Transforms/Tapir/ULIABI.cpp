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

BasicBlock * seedGeneration;
Value * prscDescLocal;
using Sync = ULIABI::Sync;
using Work = ULIABI::Work;
using PRSC_Desc = ULIABI::PRSC_Desc;

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

using PRSC_SET_JOIN_ty = void (Sync*, int);
DEFAULT_GET_LIB_FUNC(PRSC_SET_JOIN)

using PRSC_RESUME_TO_HANDLER_ty = void (int );
DEFAULT_GET_LIB_FUNC(PRSC_RESUME_TO_HANDLER)

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

    BasicBlock * curBB = Detach.getParent();
    Function * F = curBB->getParent();
    Module * M = F->getParent();
    LLVMContext& C = M->getContext();
    BasicBlock * detachBlock = Detach.getDetached();    
    BasicBlock *Continue = Detach.getContinue();
    const DataLayout &DL = M->getDataLayout();
    

    // The block is from a detach inst->continue and all the way until it finds a 
    // 1. reattach. Change the call function into a send instruction. Remove the store inst.
    // 2. Sync. Change the call function into a send instruction. Remove the store inst. 
    
    // Push continue instruction into a list.
    // If continue has a sync. Break, don't create 
    // Get the successor of the continue instruction
    // If it consists a sync. Break don't create.
    // If it consists a detach, push and jump to the achd block
    // If it consists a reattach instruction. Break but also push the block. 
    // Do a dfs. Push them into a list.
    // We assume that the cilk_spawn does not exisit in a certain branch only.
    // Check for each basic block the 
    
    // Clone the building block from the list.
    // In the clone, if there is a reattach, change a call to send instruction.
    // Remove the store instruction. 

    // Understand extract function to copy an exisiting code.     
    // Can use cloneBasicBlock
    
    // Create the work Generation
    SmallVector<BasicBlock*, 8> bbV2Clone;
    SmallVector<BasicBlock*, 8> bbList;
    DenseMap<BasicBlock *, bool> haveVisited;
    ValueToValueMapTy VMap;    
    BasicBlock * bb = nullptr;
    Instruction * term = nullptr;
    bool bIgnore = false;
    
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
            //bIgnore = true;
            //break;
        } else {
            bbV2Clone.push_back(bb);
            for( succ_iterator SI = succ_begin(bb); SI!=succ_end(bb); SI++ ){                
                bbList.push_back(*SI);
            }
        }
    }
    
    SmallVector<Instruction *,2> del_instrs;

    // Work generation for thief
    if(!bIgnore){
        DEBUG(dbgs() << "\nclone start-----------------\n " );

        for(auto BB : bbV2Clone){
            // Clone this basic block
            // modify the following instruction
            // detach->br det.achd
            // reattach->remove
            // In detach block, remove store. Change call to send instr.

            // Create a new basic block and copy instructions into it!
            BasicBlock *bbC = CloneBasicBlock(BB, VMap, ".workGen_Steal", F, nullptr,
                                      nullptr);
                        
            
            
            bbC->dump();
            VMap[BB] = bbC;
            
        }
        DEBUG(dbgs() << "\nclone end-----------------\n " );
    
        DEBUG(dbgs() << "\nremap start-----------------\n " );
        

        for(auto BB : bbV2Clone){
            // Clone this basic block
            // modify the following instruction
            // detach->br det.achd
            // reattach->remove
            // In detach block, remove store. Change call to send instr.
            BasicBlock *CBB = dyn_cast<BasicBlock>(VMap[BB]);
            Instruction *iterm  = CBB->getTerminator();
            if(DetachInst * itermDet = dyn_cast<DetachInst>(iterm)){
                BasicBlock * detachBlock = itermDet->getDetached();
                BranchInst *detachBr = BranchInst::Create(detachBlock);
                ReplaceInstWithInst(itermDet, detachBr);
            
            } else if(ReattachInst * itermRet = dyn_cast<ReattachInst>(iterm)){
                // The first instruction is a call and the the next instruction is a 
                Instruction * instr = CBB->getFirstNonPHIOrDbgOrLifetime();
                CallInst * callInst = dyn_cast<CallInst>(instr);
                assert(callInst && "First instruction not a call instruction. Seems like something is wrong");
                callInst->dump();

                SmallVector<Value*, 8> Args;
                for (int i = 0; i<callInst->getNumOperands()-1; i++){
                    //    Args.push_back(callInst->getOperand(i));
                    //callInst->getOperand(i)->dump();
                }
                
                IRBuilder<> B(instr);

                Type *VoidPtrTy = TypeBuilder<void*, false>::get(C);
                Type *PRSC_DescTy = TypeBuilder<PRSC_Desc*, false>::get(C);
                Type *Int32Ty = TypeBuilder<int32_t, false>::get(C);

                Value *InletPtr = B.CreateBitCast(F, VoidPtrTy);
                
                Args.push_back(InletPtr);

        
                Function *UliReply = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_reply);
                //CallInst * newCallInst = CallInst::Create(UliReply, Args);
                B.CreateCall(UliReply, Args);
                //newCallInst->dump();
                
                

                Value *Zero = ConstantInt::get(Int32Ty, 0, /*isSigned=*/false);
                //Value *PRSCSync = LoadSTyField(B, DL, PRSC_DescType::get(C), prscDescLocal, PRSC_DescType::sync);
                Value * PRSCSync  = B.CreateStructGEP(PRSC_DescType::get(C), prscDescLocal, (unsigned)PRSC_DescType::sync);
                prscDescLocal->dump();
                PRSCSync->dump();
                Value *PRSCpSync = B.CreateBitCast(PRSCSync, SyncType::get(C)->getPointerTo()); 
                Constant *PRSC_SET_JOIN = Get_PRSC_SET_JOIN(*M);
                B.CreateCall(PRSC_SET_JOIN, {PRSCpSync, Zero});

                Constant *PRSC_RESUME_TO_HANDLER = Get_PRSC_RESUME_TO_HANDLER(*M);
                B.CreateCall(PRSC_RESUME_TO_HANDLER, Zero);

                //DEBUG(dbgs() << "Number of operand :" << callInst->getNumOperands() << "\n");
                                               
                del_instrs.push_back(instr->getNextNode());
                del_instrs.push_back(instr);
                del_instrs.push_back(iterm);

            } else if (SyncInst * itermSync = dyn_cast<SyncInst>(iterm)){
                //TODO:
                // Find the function that can be spawned before the sync statement and its store
                // Create a reply instruction for that function and remove the store instruction after it
                // Should we also remove the remaining instruction?

            }
            
            CBB->dump();
            
            DEBUG(dbgs() << "\-------------------\n " );

            // Remap instruction
            for (Instruction &II : *CBB) {
                //II.dump();
                RemapInstruction(&II, VMap,
                                 RF_IgnoreMissingLocals,
                                 nullptr, nullptr);
            }
            
                        
        
                       

            CBB->dump();
            
        }
        DEBUG(dbgs() << "\nremap end-----------------\n " );
        

    }


    for (auto In : del_instrs){
        Instruction& inst = *In;
        inst.eraseFromParent(); // delete instrs
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
                        
            bbC->dump();
            
        }
        DEBUG(dbgs() << "\nparallel path end-----------------\n " );
    }
#endif

    //Function * replyInst = Instrinsic::getDeclaration(M, Intrinsic::x86_uli_reply);
    //B.CreateCall(replyInst, {});        

    // Start from the last detach
    
    // Get the continue block. If the block has a sync at the end of it, 
    // the at the beginning of the block you need to pop the seed (Not valid)
    // since after the last detach you can have if else meaning the sync inst.
    // is still down below
    
    // Where to push the seed? We can do it in the preprocess function instead.
    // But if there is multiple sync, we need push only when we encounter the 
    // first detach

    // Get the achd block. Add a potential Jump to the seed generation
   
   IRBuilder<> builder(&*detachBlock->getFirstInsertionPt());
   Function * potentialJump = Intrinsic::getDeclaration(M, Intrinsic::x86_uli_potential_jump);
   Type *VoidPtrTy = TypeBuilder<void*, false>::get(C);
   //Value * NULLPTR = ConstantPointerNull::get(IntegerType::getInt64Ty(Detach.getContext())->getPointerTo());
   
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
   reattach->dump();
   //ReplaceInstWithInst(reattach, ContinueBr);
   
   
   
   
    // Flow is similar to Cilk, except that we don't need a helper function and
    // just directly call the function
    

    // change the detach into branch into detach block
    // chang reattach into branch into continue block
    // in other words
    // Change the flow of the det.achd and det.continue
    // det.achd -> det.continue
    // Can I use populate Detached CFG?

    // How to change the detach instruction. Look at createDetach since it changes the detach instrcution
  
    // Extract function here to get the seed generation for suspend and steal
   

   

    
   //assert(false);
  return nullptr;
}


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
  
  // Generate the seed generation here  
  {
    seedGeneration = BasicBlock::Create(C, "seedGen", &F);
    seedGeneration->dump();
    
  }

  F.dump();
  

  //assert(false);
}

void ULIABI::postProcessFunction(Function &F) {
    // Generate the parallel path here and do some fix up?
    
    // Generate the gotStolen path and the ready thread sync resume here
    
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

