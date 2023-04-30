//===- ULIIntrinsicToExternCall.cpp - Emulate ULI intrinsics --------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass replace ULI intrinsics with external calls to the ULI emulation
// library.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/ULI/ULIIntrinsicToExternCall.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#define SV_NAME "uli-int2ext"
#define DEBUG_TYPE "ULI"

namespace {

/// The ULI intrinsic to external call pass (legacy).
struct ULIIntrinsicToExternCall : public FunctionPass {

  /// Pass identification, replacement for type id.
  static char ID;

  // Construct and initialize the pass.
  explicit ULIIntrinsicToExternCall() : FunctionPass(ID) {
  }

  /// \return If we change anything in function \p F.
  virtual bool runOnFunction(Function &F) override {
    // Get required analysis.
    // We need dominator analysis because we need to find valid positions to
    // insert alloca instructions for storing return values of extern calls.
    auto *DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();

    // essentially delegating all work to the code which is setup to use the new pass manager
    return Impl.runImpl(F, DT);
  }

  /// \brief Specify required analysis and preserve analysis that is not
  /// affected by this pass.
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.setPreservesCFG();
  }

private:
  /// Real implementation.
  ULIIntrinsicToExternCallPass Impl;
};

} // end anonymous namespace

void ULIIntrinsicToExternCallPass::initializeIntrinsicExternMap(Module &M) {
  // Get all functions of ULI intrinsics and the corresponding extern names. We
  // first add intrinsics that have the same type as extern functions. They can
  // be easily rewritten by redirecting the existing arguments.
  IntrinsicExternMap.clear();
  SmallVector<std::pair<Intrinsic::ID, std::string>, 4> SameTypeIntrinsics = {
      {Intrinsic::uli_enable, "ENAULI"},
      {Intrinsic::uli_disable, "DISULI"},
      {Intrinsic::uli_set, "SETULI"},
      {Intrinsic::uli_read, "READULI"},
      {Intrinsic::uli_rdrdi, "RDULIRDI"},
      {Intrinsic::uli_rdflags, "RDULIFLAGS"},
      {Intrinsic::uli_rdRA, "RDULIRA"},
      {Intrinsic::uli_wrrdi, "WRULIRDI"},
      {Intrinsic::uli_wrflags, "WRULIFLAGS"},
      {Intrinsic::uli_wrRA, "WRULIRA"},
      {Intrinsic::uli_atomic, "SETULIATOMIC"},
      {Intrinsic::uli_getcpu, "getpid"}};
  for (const auto &I : SameTypeIntrinsics) {
    const bool IsSameType  = true;
    Function *IF           = Intrinsic::getDeclaration(&M, I.first);
    IntrinsicExternMap[IF] = {
        I.first, I.second, IF->getFunctionType(), IsSameType};
  }

  // Next we add intrinsics that need manipulating the existing arguments.
  SmallVector<std::pair<Intrinsic::ID, std::string>, 4> DiffTypeIntrinsics = {
      {Intrinsic::uli_send0cN, "SENDI"},
      {Intrinsic::uli_reply0cN, "REPLYI"},
      {Intrinsic::uli_toireg, "TOIREG"},
      {Intrinsic::uli_fromireg, "FROMIREG"}};
  for (const auto &I : DiffTypeIntrinsics) {
    const bool IsSameType  = false;
    Function *IF           = Intrinsic::getDeclaration(&M, I.first);
    IntrinsicExternMap[IF] = {
        I.first, I.second, IF->getFunctionType(), IsSameType};
  }
}

// used for handler functions
void ULIIntrinsicToExternCallPass::insertExternReturns(Function &F) {
  // Insert extern declaration (if needed) and call.
  Module &M               = *F.getParent();
  Type *VoidTy            = Type::getVoidTy(M.getContext());
  FunctionType *ExternFTy = FunctionType::get(VoidTy, false);
  FunctionCallee ExternFunc    = M.getOrInsertFunction("RETULI", ExternFTy);

  // We insert before each return instruction.
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    if (ReturnInst *ReturnInstr = dyn_cast<ReturnInst>(&*I))
      CallInst::Create(ExternFunc, "", ReturnInstr);
  }
}

void ULIIntrinsicToExternCallPass::collectIntrinsicCalls(Function &F) {
  // Collect intrinsic calls that we can rewrite.
  IntrinsicCalls.clear();
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    if (auto *CallInstr = dyn_cast<CallInst>(&*I)) {
      Function *CalledFunc = CallInstr->getCalledFunction();
      // If we have corresponding extern function, we can rewrite it.
      if (IntrinsicExternMap.count(CalledFunc))
        IntrinsicCalls.push_back(CallInstr);
    }
  }
}

CallInst *ULIIntrinsicToExternCallPass::rewriteToExternSameType(
    CallInst *IntrinsicCI, const ExternCall &Extern, Module &M) {
  // Insert extern declaration (if needed) and call.
  FunctionCallee ExternFunc = M.getOrInsertFunction(Extern.Name, Extern.FTy);

  // Copy all function arguments.
  SmallVector<Value *, 4> Args;
  for (unsigned AI = 0, AE = IntrinsicCI->arg_size(); AI < AE; ++AI)
    Args.push_back(IntrinsicCI->getArgOperand(AI));

  // Insert extern call and remove the intrinsic call.
  CallInst *ExternCI = CallInst::Create(ExternFunc, Args, "", IntrinsicCI);
  IntrinsicCI->replaceAllUsesWith(ExternCI);
  IntrinsicCI->eraseFromParent();

  return ExternCI;
}

CallInst *ULIIntrinsicToExternCallPass::rewriteToExternDiffType(
    CallInst *IntrinsicCI, const ExternCall &Extern, Module &M) {
  // Prepare common argument types.
  LLVMContext &Ctx = M.getContext();
  Type *VoidTy     = Type::getVoidTy(Ctx);
  Type *Int8Ty     = Type::getInt8Ty(Ctx);
  Type *Int32Ty    = Type::getInt32Ty(Ctx);
  Type *Int64Ty    = Type::getInt64Ty(Ctx);
  Type *Int64PtrTy = Type::getInt64PtrTy(Ctx);

  // Insert extern declaration and manipulate the arguments based on the type of
  // intrinsic.
  CallInst *ExternCI = nullptr;
  IRBuilder<> Builder(Ctx);
  switch (Extern.ID) {
  case Intrinsic::uli_send0c: {
    // Get the extern function.
    SmallVector<Type *, 4> ArgsTy = {Int32Ty, Int8Ty, Int64Ty, Int32Ty};
    FunctionType *ExternTy = FunctionType::get(VoidTy, ArgsTy, false);
    FunctionCallee ExternFunc   = M.getOrInsertFunction(Extern.Name, ExternTy);

    // Manipulate the arguments so that we can pass them to the new extern call.
    Builder.SetInsertPoint(IntrinsicCI);
    Value *C32   = ConstantInt::get(Int64Ty, 32);
    Value *CZero = ConstantInt::get(Int32Ty, 0);

    // Intrinsic argument 1 = [ destination proc id, interrupt number ]
    //                                 32-bit              8-bit
    Value *Arg1   = IntrinsicCI->getArgOperand(0);
    Value *DestID = Builder.CreateLShr(Arg1, C32);
    DestID        = Builder.CreateTrunc(DestID, Int32Ty);
    Value *IntNum = Builder.CreateTrunc(Arg1, Int8Ty);

    // Intrinsic argument 2 = handler address.
    Value *Handler = IntrinsicCI->getArgOperand(1);
    Handler        = Builder.CreatePtrToInt(Handler, Int64Ty);
    SmallVector<Value *, 4> Args = {DestID, IntNum, Handler, CZero};

    // Insert extern call and remove the intrinsic call.
    ExternCI = Builder.CreateCall(ExternFunc, Args);
    IntrinsicCI->replaceAllUsesWith(ExternCI);
    IntrinsicCI->eraseFromParent();
    break;
  }
  case Intrinsic::uli_send0cN: {
    // Get the extern function.

    SmallVector<Type *, 4> ArgsTy = {Int32Ty, Int8Ty, Int64Ty, Int32Ty};
    FunctionType *ExternTy = FunctionType::get(VoidTy, ArgsTy, false);
    FunctionCallee ExternFunc   = M.getOrInsertFunction(Extern.Name, ExternTy);

    // Manipulate the arguments so that we can pass them to the new extern call.
    Builder.SetInsertPoint(IntrinsicCI);
    Value *C32   = ConstantInt::get(Int64Ty, 32);
    Value *CZero = IntrinsicCI->getArgOperand(2);

    // Intrinsic argument 1 = [ destination proc id, interrupt number ]
    //                                 32-bit              8-bit
    Value *Arg1   = IntrinsicCI->getArgOperand(0);
    Value *DestID = Builder.CreateLShr(Arg1, C32);
    DestID        = Builder.CreateTrunc(DestID, Int32Ty);
    Value *IntNum = Builder.CreateTrunc(Arg1, Int8Ty);

    // Intrinsic argument 2 = handler address.
    Value *Handler = IntrinsicCI->getArgOperand(1);
    Handler        = Builder.CreatePtrToInt(Handler, Int64Ty);
    SmallVector<Value *, 4> Args = {DestID, IntNum, Handler, CZero};

    // Insert extern call and remove the intrinsic call.
    ExternCI = Builder.CreateCall(ExternFunc, Args);
    IntrinsicCI->replaceAllUsesWith(ExternCI);
    IntrinsicCI->eraseFromParent();
    break;
  }
  case Intrinsic::uli_reply0c: {
    // Get the extern function.
    assert(0);			// we don't use this intrinsic anymore
    SmallVector<Type *, 2> ArgsTy = {Int64Ty, Int32Ty};
    FunctionType *ExternTy = FunctionType::get(VoidTy, ArgsTy, false);
    FunctionCallee ExternFunc   = M.getOrInsertFunction(Extern.Name, ExternTy);

    // Manipulate the arguments so that we can pass them to the new extern call.
    Builder.SetInsertPoint(IntrinsicCI);
    Value *CZero = IntrinsicCI->getArgOperand(1); // ConstantInt::get(Int32Ty, 0);

    // Intrinsic argument 1 = handler address.
    Value *Handler = IntrinsicCI->getArgOperand(0);
    Handler        = Builder.CreatePtrToInt(Handler, Int64Ty);
    SmallVector<Value *, 2> Args = {Handler, CZero};

    // Insert extern call and remove the intrinsic call.
    ExternCI = Builder.CreateCall(ExternFunc, Args);
    IntrinsicCI->replaceAllUsesWith(ExternCI);
    IntrinsicCI->eraseFromParent();
    break;
  }
  case Intrinsic::uli_reply0cN: {
    // Get the extern function.
    SmallVector<Type *, 2> ArgsTy = {Int64Ty, Int32Ty};
    FunctionType *ExternTy = FunctionType::get(VoidTy, ArgsTy, false);
    FunctionCallee ExternFunc   = M.getOrInsertFunction(Extern.Name, ExternTy);

    // Manipulate the arguments so that we can pass them to the new extern call.
    Builder.SetInsertPoint(IntrinsicCI);
    Value *CZero = IntrinsicCI->getArgOperand(1); // number of args to this reply

    // Intrinsic argument 1 = handler address.
    Value *Handler = IntrinsicCI->getArgOperand(0);
    Handler        = Builder.CreatePtrToInt(Handler, Int64Ty);
    SmallVector<Value *, 2> Args = {Handler, CZero};

    // Insert extern call and remove the intrinsic call.
    ExternCI = Builder.CreateCall(ExternFunc, Args);
    IntrinsicCI->replaceAllUsesWith(ExternCI);
    IntrinsicCI->eraseFromParent();
    break;
  }
  case Intrinsic::uli_toireg: {
    // Get the extern function.
    SmallVector<Type *, 2> ArgsTy = {Int64Ty, Int8Ty};
    FunctionType *ExternTy = FunctionType::get(VoidTy, ArgsTy, false);
    FunctionCallee ExternFunc   = M.getOrInsertFunction(Extern.Name, ExternTy);

    // Manipulate the arguments so that we can pass them to the new extern call.
    Builder.SetInsertPoint(IntrinsicCI);
    // Intrinsic argument 1 = ULI register number.
    Value *RegNum = IntrinsicCI->getArgOperand(0);
    RegNum        = Builder.CreateTrunc(RegNum, Int8Ty);
    // Intrinsic argument 2 = ULI register value.
    Value *RegVal = IntrinsicCI->getArgOperand(1);
    SmallVector<Value *, 2> Args = {RegVal, RegNum};
    // Insert extern call and remove the intrinsic call.
    ExternCI = Builder.CreateCall(ExternFunc, Args);
    IntrinsicCI->replaceAllUsesWith(ExternCI);
    IntrinsicCI->eraseFromParent();
    break;
  }
  case Intrinsic::uli_fromireg: {
    // Get the extern function.
    SmallVector<Type *, 2> ArgsTy = {Int8Ty, Int64PtrTy};
    FunctionType *ExternTy = FunctionType::get(VoidTy, ArgsTy, false);
    FunctionCallee ExternFunc   = M.getOrInsertFunction(Extern.Name, ExternTy);

    // Manipulate the arguments so that we can pass them to the new extern call.
    // We need to allocate a temp value since the extern function would modify
    // that via pointer.
    BasicBlock *CallBlock  = IntrinsicCI->getParent();
    Function *F            = CallBlock->getParent();
    BasicBlock *EntryBlock = &F->getEntryBlock();
    if (!DT->dominates(EntryBlock, CallBlock))
      return nullptr;
    Builder.SetInsertPoint(EntryBlock->getFirstNonPHI());
    AllocaInst *Temp = Builder.CreateAlloca(Int64Ty);

    // Intrinsic argument 1 = ULI register number.
    Builder.SetInsertPoint(IntrinsicCI);
    Value *RegNum = IntrinsicCI->getArgOperand(0);
    RegNum        = Builder.CreateTrunc(RegNum, Int8Ty);
    SmallVector<Value *, 2> Args = {RegNum, Temp};

    // Insert extern call and load the output value of extern call.
    ExternCI      = Builder.CreateCall(ExternFunc, Args);
    Value *Output = Builder.CreateLoad(Int64Ty, Temp);
    IntrinsicCI->replaceAllUsesWith(Output);
    IntrinsicCI->eraseFromParent();
    break;
  }
  default:
    // TODO: Handle other intrinsic in the spec if needed.
    llvm_unreachable("Unexpected intrinsic function");
  }

  return ExternCI;
}

bool ULIIntrinsicToExternCallPass::rewriteToExtern(
    ArrayRef<CallInst *> IntrinsicCalls, Module &M) {
  // For each ULI intrinsic call, rewrite to mapped extern call.
  bool Changed = false;
  for (CallInst *IntrinsicCI : IntrinsicCalls) {
    Function *IntrinsicFunc  = IntrinsicCI->getCalledFunction();
    const ExternCall &Extern = IntrinsicExternMap.lookup(IntrinsicFunc);

    // Rewrite to extern call.
    if (Extern.SameTy) {
      if (rewriteToExternSameType(IntrinsicCI, Extern, M))
        Changed = true;
    } else {
      if (rewriteToExternDiffType(IntrinsicCI, Extern, M))
        Changed = true;
    }
  }

  return Changed;
}

bool ULIIntrinsicToExternCallPass::runImpl(Function &F, DominatorTree *DT_) {
  // Get required analysis.
  DT = DT_;

  // If current function is ULI handler (using ULI calling convention), rewrite
  // its convention to default C and insert an extern call to ULI return.
  bool Changed = false;
  if (F.getCallingConv() == CallingConv::X86_ULI) {
    stripULICallingConvention(F);
    insertExternReturns(F);
    Changed = true;
  }

  // Collect all ULI intrinsic calls and rewrite to extern calls.
  Module &M = *F.getParent();
  initializeIntrinsicExternMap(M);
  collectIntrinsicCalls(F);
  Changed |= rewriteToExtern(IntrinsicCalls, M);
  return Changed;
}

PreservedAnalyses
ULIIntrinsicToExternCallPass::run(Function &F, FunctionAnalysisManager &AM) {
  // Get required analysis.
  // We need dominator analysis because we need to find valid positions to
  // insert alloca instructions for storing return values of extern calls.
  auto *DT = &AM.getResult<DominatorTreeAnalysis>(F);

  // Run on function.
  bool Changed = runImpl(F, DT);
  if (!Changed)
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}

////////////////////////////////////////////////////////////////
// this starts the legacy pass manager code, above here is for new
// pass manager (except for the decl of the structure at the top)
////////////////////////////////////////////////////////////////


char ULIIntrinsicToExternCall::ID = 0;

static const char lv_name[] = "ULI Intrinsic to external call";

Pass *llvm::createULIIntrinsicToExternCallPass() {
  return new ULIIntrinsicToExternCall();
}
