//===- Forkable.cpp - Based on Example code from "Writing an LLVM Pass" ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the module pass to create the wrappers for
// forkable functions
//
//===----------------------------------------------------------------------===//

#include <unordered_map>

#include "llvm/AsmParser/Parser.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "forkable"

STATISTIC(ForkableCounter, "Counts number of functions checked");

namespace {
  // forkable - The first implementation, without getAnalysisUsage.
  struct Forkable : public ModulePass {

  private:
    bool changed = false;	// have we changed anything in this module?
    Module* thisModule = NULL;	// the module we are working on
    Type* returnType = NULL;	// the return type for the function we are creating a wrapper for
    Function* wrapper = NULL;	// current wrapper being generated
    BasicBlock* wrapperEntryBlock = NULL; // entry block for current wrapper being generated
    static int uid;		// used to generate uniq ids


    void insertEUI(void) {
      // need to implement this
      assert(0);
    }

    ////////////////////////////////////////////////////////////////
    // CLASS TO PARSE ASM CONSTRAINTS WE USE TO BUILD CODE HERE
    class AsmStmt {
    private:
      std::string text;		// assembly code possibly with [names]
      bool converted;		// if text has replaced [names] with %numbers
      bool sideEffect;		// whether side effect is true
      std::string constraintStr;		// constraints.  output, then input, then clobber
      std::vector<Type *> argTypes;			// types for all args (see constraints above)
      FunctionType *funcType;				// function type for this asminline
      std::string rettype;	   	// if return type, then ignore first output
      std::vector<std::string> outs;
      std::vector<std::string> ins;
      std::vector<const char*> argtypes;
      std::vector<const char*> clobbers;

      static unsigned int labelid; // used for generating uniq goto labels

      // parse conlist so that each mentioned var gets an argnumber.
      // record its contraint.  also, push constraint onto master list
      // conlist is a list of constraints, s.t., name:constraint
      // add name -> num into name2num
      // add name -> constraint into name2constraint
      // we start numbering from argnum
      // also, put all the constraints into the constraints member var
      // return updated argnum so we can keep doing this with other lists
      unsigned int parseContraints(std::vector<std::string>& constraints,
				   std::unordered_map<std::string, unsigned int>& name2num,
				   std::unordered_map<std::string, std::string>& name2constraint,
				   unsigned int argnum,
				   std::vector<std::string> conlist) {
	for (const auto& str: conlist) {
	  std::size_t splitter = str.find_first_of(':');
	  assert(splitter != std::string::npos && "We expected a ':' between the name and the constraint");
	  std::string name = std::string(str, 0, splitter);
	  std::string constraint = std::string(str, splitter+1);
	  name2num[name] = argnum;
	  name2constraint[name] = constraint;
	  constraints.push_back(constraint);
	  errs() << name << ":\t" << argnum << "\t" << constraint << "\n";
	  argnum++;
	}
	return argnum;
      }

      void makeTypes(Module& M) {
	// create return type
	SMDiagnostic smd;
	Type* retType = llvm::parseType(rettype, smd, M);

	// create arg types
	for (auto tystr: argtypes) {
	  Type* t = llvm::parseType(tystr, smd, M);
	  argTypes.push_back(t);
	}

	// create function type
	funcType = FunctionType::get(retType, argTypes, false);
      }

      // replace all occurences of from to to in text.
      // return number of replacements that occur
      unsigned replaceAll(const std::string from, const std::string to) {
	unsigned cnt = 0;
	if (text.find(from) != std::string::npos) {
	  size_t pos = text.find(from);
	  size_t len = from.size();
	  errs () << pos << ", " << len << "\n";
	  while( pos != std::string::npos) {
	    // Replace this occurrence of name with num
	    text.replace(pos, len, to);
	    // Get the next occurrence from the current position
	    pos =text.find(from, pos + 1);
	    cnt++;
	  }
	}
	return cnt;
      }

      void convertCode(Module& M) {
	if (converted) return;

	// create a map of names to numbers and constraints
	std::vector<std::string> constraints;		// constraints.  output, then input, then clobber
	std::unordered_map<std::string, unsigned int> name2num;
	std::unordered_map<std::string, std::string> name2constraint;
	unsigned int argnum = 0;
	argnum = parseContraints(constraints, name2num, name2constraint, argnum, outs);
	argnum = parseContraints(constraints, name2num, name2constraint, argnum, ins);

	// add on all clobbers
	for (const auto& clobber: clobbers) {
	  constraints.push_back(clobber);
	}
	constraints.push_back("~{dirflag}");
	constraints.push_back("~{fpsr}");
	constraints.push_back("~{flags}");

	// create constraint string
	constraintStr = "";
	std::string sep = "";
	for (auto c : constraints) {
	  constraintStr += (sep + c);
	  sep = ",";
	}
	// create converted code %[xxx] -> $<num>
	errs() << text << "\n\t == Becomes ==> \n";
	for( const auto& pair : name2num ) {
	  const auto name = "%[" + pair.first + "]";
	  const auto num = "$" + std::to_string(pair.second);
	  errs() << "\t" << name << " will become " << num << "\n";
	  if (replaceAll(name, num) == 0) {
	    errs() << "==> " << name << " Not found in asm string\n";
	  }
	}
	// now replace %% with %
	replaceAll("%%", "%");

	errs() << text << "\n";
	makeTypes(M);
	converted = true;
      }
    public:
      AsmStmt(StringRef code,
	      bool hasSideEffect,
	      std::vector<std::string> outs, // array of name:constraint
	      std::vector<std::string> ins,  // array of name:constraint
	      std::string rettype,	   // if return type, then ignore first output
	      std::vector<const char*> argtypes,
	      std::vector<const char*> clobbers) : text(code),
						   converted(false),
						   sideEffect(hasSideEffect),
						   rettype(rettype),
						   outs(outs),
						   ins(ins),
						   argtypes(argtypes),
						   clobbers(clobbers)
      {
      }

      InlineAsm* getInlineAsm(Module& m) {
	convertCode(m);
	InlineAsm *ia = InlineAsm::get(funcType, text, constraintStr, sideEffect,
				       /* IsAlignStack */ false, InlineAsm::AD_ATT);
	return ia;
      }
      };

  public:
    static char ID; // Pass identification, replacement for typeid
    Forkable() : ModulePass(ID) {}

    // check to see if the wrapper version of this function already exists
    bool hasWrapper(Function& F) {
      return false;
    }

    // create a wrapper version of this function
    Function* createWrapper(Function& F) {
      LLVMContext &ctx = thisModule->getContext();

      // here we create a new function that is wrapper of this function definition
      FunctionType* fType = F.getFunctionType();
      // Find out the return value.
      returnType = fType->getReturnType();
      // make new type, same as old, but with void return type
      // (see also ~/research/uli/src/compiler/llvm/lib/Transforms/Utils/CloneFunction.cpp:239)
      FunctionType* newFuncType = FunctionType::get(Type::getVoidTy(ctx), fType->params(), fType->isVarArg());
      Function* newFunction = Function::Create(newFuncType, F.getLinkage(), F.getName() + "Wrapper", F.getParent());

      // give arguments actual parameter names
      auto NewFArgIt = newFunction->arg_begin();
      for (auto &Arg: F.args()) {
	auto ArgName = Arg.getName();
	NewFArgIt->setName(ArgName);
	NewFArgIt++;
      }

      newFunction->dump();
      changed = true;
      wrapper = newFunction;
      return newFunction;
    }

    // allocate name with type in entry block of wrapper function.  If name is NULL, create a tmp name
    AllocaInst *allocLocalVariable(const char* name, Type* type)
    {
      char buffer[128];

      if (name == NULL) {
	name = buffer;
	sprintf(buffer, "tmpvar%d", uid);
	uid++;
      }
      IRBuilder<> TmpB(wrapperEntryBlock, wrapperEntryBlock->begin());
      return TmpB.CreateAlloca(type, 0, name);
    }

    // add the asm stmt with the args as specified to the basicblock
    Value* addAsm(AsmStmt& stmt, BasicBlock *bb, std::vector<Value *> asmArgs) {
      InlineAsm *ia = stmt.getInlineAsm(*thisModule);
      Value* ret = CallInst::Create(ia, asmArgs, "", bb);
      return ret;
    }

#if 0
    void skip(LLVMContext &ctx, BasicBlock *bb, StringRef asmText, StringRef constraints) {
      std::vector<Type *> asmArgTypes;
      std::vector<Value *> asmArgs;

      FunctionType *asmFTy =
	FunctionType::get(Type::getVoidTy(ctx), asmArgTypes, false);
      InlineAsm *ia = InlineAsm::get(asmFTy, asmText, "", true,
				     /* IsAlignStack */ false, InlineAsm::AD_ATT);
      CallInst::Create(ia, asmArgs, "", bb);
    }
#endif

    bool runOnModule(Module &M) override {
      thisModule = &M;
      LLVMContext &ctx = thisModule->getContext();
      changed = false;

      ++ForkableCounter;
      for (Function &F : M) {
	errs() << "---------------Looking at : \n";
	errs().write_escaped(F.getName());
	errs() << "\n";
	F.getFunctionType()->dump();
	if (F.hasFnAttribute(Attribute::Forkable)) {
	  errs() << " is FORKABLE\n";
	  // whether a declaration of a definition we need to create the wrapper version
	  // How do we find out if wrapper is already in the module??
	  if (hasWrapper(F)) continue;
	  Function* WrapperFunction = createWrapper(F);
	  if (F.isDeclaration()) {
	    errs() << F.getName() << " is a declaration\n";
	    continue;
	  }
	  //
	  // here we add the body to the function
	  //
	  BasicBlock* block = BasicBlock::Create(ctx, "entry", wrapper, 0);
	  IRBuilder<> builder(ctx);
	  builder.SetInsertPoint(block);
	  wrapperEntryBlock = block;

	  // get sp and then stub
	  /*AsmStmt addsp{"#getsp\n\tmovq %%rsp,%[Var]",
	      true,
		{"Var:=r"},
		  {},
		    "i8*",
		      {},
			{}};
	  Value* sp = addAsm(addsp, block, {});*/
	  Function *readsp = Intrinsic::getDeclaration(&M, Intrinsic::x86_read_sp);
	  Value* sp = builder.CreateCall(readsp);

	  // lets test this out with a call to printvp
	  Type* Int8PtrType = Type::getInt8PtrTy(thisModule->getContext());
	  Type* IntType = Type::getIntNTy(thisModule->getContext(), 32);
	  auto* PFtype = FunctionType::get(Type::getVoidTy(ctx), {Int8PtrType, IntType}, false);

	  Constant *PF = thisModule->getOrInsertFunction("printvp", PFtype);
	  PF->dump();
	  sp->dump();
	  SmallVector<Value *, 4> pvArgs;
	  pvArgs.push_back(sp);
	  for (auto &Arg: wrapper->args()) {
	    pvArgs.push_back(&Arg);
	  }
	  builder.CreateCall(PF, pvArgs);

	  // get stacklet stub adr from sp
	  SMDiagnostic smd;
	  Type* stubType = llvm::parseType("%struct.stubstruct", smd, *thisModule);
	  Type* ptr2Stub = PointerType::getUnqual(stubType);
	  auto* getStubType = FunctionType::get(ptr2Stub, {Int8PtrType}, false);
	  errs() << "Looking up getStubAdr\n";
	  stubType->dump();
	  ptr2Stub->dump();
	  getStubType->dump();
	  Constant* getStub = thisModule->getOrInsertFunction("getStubAdr", getStubType);
	  Value* stubadr = builder.CreateCall(getStub, {sp});
	  {
	    SmallVector<Value *, 4> argsV;
	    Value* vpStubadr = builder.CreateBitCast(stubadr, Int8PtrType);
	    argsV.push_back(vpStubadr);
	    argsV.push_back(ConstantInt::get(llvm::Type::getInt32Ty(thisModule->getContext()), 1));
	    builder.CreateCall(PF, argsV);
	  }

	  // declare the return value
	  //AllocaInst *retValue = allocLocalVariable("rval", returnType);

	  // construct call to original function
	  SmallVector<Value *, 4> argsV;

	  for (auto &arg: wrapper->args()) {
	    argsV.push_back(&arg);
	  }
	  //CallInst* ci =
	  builder.CreateCall(&F, argsV, "rval");
	  builder.CreateRetVoid();

	  // enable UI
	  //insertEUI();

	  // return value



	  WrapperFunction->dump();

	} else {
	  errs() << "==============================\n";
	}
      }
      // clean up
      thisModule = NULL;
      returnType = NULL;
      wrapper = NULL;
      wrapperEntryBlock = NULL;
      return changed;
    }

#if 0
    // We don't modify the program, so we preserve all analyses.
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
    }
#endif
  };
}

char Forkable::ID = 0;
int Forkable::uid = 0;
static RegisterPass<Forkable> X("forkable", "Forkable Pass");
