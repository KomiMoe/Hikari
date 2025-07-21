#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Obfuscation/IndirectGlobalVariable.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/APInt.h"

#include <random>

#define DEBUG_TYPE "indgv"

using namespace llvm;
namespace {
struct IndirectGlobalVariable : public FunctionPass {
  unsigned pointerSize;
  static char ID;
  
  ObfuscationOptions *ArgsOptions;
  std::map<GlobalVariable *, unsigned> GVIndex;
  std::vector<GlobalVariable *> GVPage;
  std::map<Function *, std::vector<GlobalVariable *>> FunctionGVs;
  std::vector<GlobalVariable *> GlobalVariables;
  CryptoUtils RandomEngine;
  Constant *ModuleKey = nullptr;
  bool RunOnFuncChanged = false;

  IndirectGlobalVariable(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  StringRef getPassName() const override { return {"IndirectGlobalVariable"}; }

  void NumberGlobalVariable(Module &M) {
    for (auto &F : M) {
      if (F.isIntrinsic()) {
        continue;
      }
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        Instruction *Inst  = &*I;

        if (Inst->isEHPad() || isa<CallInst>(Inst)) {
          continue;
        }

        for (auto op = Inst->op_begin(); op != Inst->op_end(); ++op) {
          Value *val = *op;
          if (auto GV = dyn_cast<GlobalVariable>(val)) {
            if (GV->isThreadLocal() || GV->isDLLImportDependent()) {
              continue;
            }
            if (std::find(FunctionGVs[&F].begin(), FunctionGVs[&F].end(), GV)
                == FunctionGVs[&F].end()) {
              FunctionGVs[&F].push_back(GV);
            }

            if (GVIndex.count(GV) == 0) {
              GVIndex[GV] = 0;
              GlobalVariables.push_back(GV);
            }
          }
        }
      }
    }
  }

  bool doInitialization(Module &M) override {
    GVIndex.clear();
    GVPage.clear();
    FunctionGVs.clear();
    GlobalVariables.clear();
    auto Int32Ty = IntegerType::getInt32Ty(M.getContext());
    ModuleKey = ConstantInt::get(Int32Ty, RandomEngine.get_uint32_t());

    for (auto &Fn : M) {
      if (Fn.isIntrinsic()) {
        continue;
      }
      LowerConstantExpr(Fn);
    }
    NumberGlobalVariable(M);
    if (GlobalVariables.empty()) {
      return false;
    }
    auto seed = RandomEngine.get_uint64_t();
    std::default_random_engine e(seed);
    std::shuffle(GlobalVariables.begin(), GlobalVariables.end(), e);

    std::vector<Constant *> GVGVs;
    for (unsigned i = 0; i < GlobalVariables.size(); ++i) {
      auto GV = GlobalVariables[i];
      GVGVs.push_back(ConstantExpr::getBitCast(GV, PointerType::getUnqual(M.getContext())));
      GVIndex[GV] = i;
    }

    {
      std::string GVNameGVs(M.getName().str() + "_IndirectGVs");
      ArrayType *ATy = ArrayType::get(GVGVs[0]->getType(), GVGVs.size());
      Constant *CA = ConstantArray::get(ATy, ArrayRef(GVGVs));
      auto GV = new GlobalVariable(M, ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
        CA, GVNameGVs);
      GVPage.push_back(GV);
    }

    for (unsigned i = 0; i < 1; ++i) {
      seed = RandomEngine.get_uint64_t();
      e = std::default_random_engine(seed);
      std::shuffle(GlobalVariables.begin(), GlobalVariables.end(), e);

      std::vector<Constant *> ConstantGVIndex;
      for (unsigned j = 0; j < GlobalVariables.size(); ++j) {
        auto GV = GlobalVariables[j];
        APInt preIndex(32, GVIndex[GV]);
        preIndex = preIndex.rotl(j);
        Constant *toWriteData = ConstantInt::get(Int32Ty, preIndex);
        toWriteData = ConstantExpr::getXor(toWriteData, ModuleKey);
        toWriteData = ConstantExpr::getAdd(toWriteData, ConstantInt::get(Int32Ty, j));
        ConstantGVIndex.push_back(toWriteData);
        GVIndex[GV] = j;
      }

      {

        std::string GVNameGVPage(M.getName().str() + "_IndirectGVPage_" + std::to_string(i));
        auto IATy = ArrayType::get(Int32Ty, ConstantGVIndex.size());
        auto IA = ConstantArray::get(IATy, ArrayRef(ConstantGVIndex));
        auto GV = new GlobalVariable(M, IATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
          IA, GVNameGVPage);
        GVPage.push_back(GV);
      }
    }
    return false;
  }


  bool runOnFunction(Function &Fn) override {
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->indGvOpt(), &Fn);
    if (!opt.isEnabled()) {
      return false;
    }

    LLVMContext &Ctx = Fn.getContext();
    auto& M = *Fn.getParent();


    if (GlobalVariables.empty()) {
      return false;
    }

    auto& FuncGVs = FunctionGVs[&Fn];
    if (FunctionGVs.empty()) {
      return false;
    }

    auto Int32Ty = IntegerType::getInt32Ty(Ctx);
    auto Zero = ConstantInt::getNullValue(Int32Ty);
    ConstantInt *FuncKey = ConstantInt::get(Int32Ty, RandomEngine.get_uint32_t());

    std::vector<GlobalVariable *> FuncGVPage;
    std::map<GlobalVariable *, unsigned> FuncGVIndex;
    for (unsigned i = 0; i < opt.level(); ++i) {
      auto seed = RandomEngine.get_uint64_t();
      auto e = std::default_random_engine(seed);
      std::shuffle(FuncGVs.begin(), FuncGVs.end(), e);

      std::vector<Constant *> ConstantGVIndex;
      for (unsigned j = 0; j < FuncGVs.size(); ++j) {
        auto GV = FuncGVs[j];

        APInt preIndex(32, FuncGVIndex.find(GV) == FuncGVIndex.end() ?
                             GVIndex[GV] :
                             FuncGVIndex[GV]);
        
        preIndex = preIndex.rotr(j);
        Constant *toWriteData = ConstantInt::get(Int32Ty, preIndex);
        toWriteData = ConstantExpr::getXor(toWriteData, FuncKey);
        if (opt.level() > 1) {
          toWriteData = ConstantExpr::getSub(toWriteData, ConstantInt::get(Int32Ty, j));
        }
        if (opt.level() > 2) {
          toWriteData = ConstantExpr::getNeg(toWriteData);
        }
        ConstantGVIndex.push_back(toWriteData);
        FuncGVIndex[GV] = j;
      }

      {
        std::string GVNameGVPage(M.getName().str() + "_" + Fn.getName().str() + "_IndirectGVPage_" + std::to_string(i));
        auto IATy = ArrayType::get(Int32Ty, ConstantGVIndex.size());
        auto IA = ConstantArray::get(IATy, ArrayRef(ConstantGVIndex));
        auto GV = new GlobalVariable(M, IATy, false, GlobalValue::LinkageTypes::InternalLinkage,
          IA, GVNameGVPage);
        FuncGVPage.push_back(GV);
      }
    }


    for (inst_iterator I = inst_begin(Fn), E = inst_end(Fn); I != E; ++I) {
      Instruction *Inst = &*I;
      if (isa<CallInst>(Inst) || isa<CatchReturnInst>(Inst) || isa<ResumeInst>(Inst) || Inst->isEHPad()) {
        continue;
      }

      for (unsigned i = 0; i < Inst->getNumOperands(); ++i) {
        if (GlobalVariable *GV = dyn_cast<GlobalVariable>(Inst->getOperand(i))) {
          if (!GVIndex.count(GV)) {
            continue;
          }

          PHINode *PHI = dyn_cast<PHINode>(Inst);
          IRBuilder<> IRB(PHI ? PHI->getIncomingBlock(i)->getTerminator() : Inst);

          Value *NextIndex = FuncGVIndex.find(GV) == FuncGVIndex.end() ?
            ConstantInt::get(Int32Ty, GVIndex[GV]) :
            ConstantInt::get(Int32Ty, FuncGVIndex[GV]) ;

          for (int j = FuncGVPage.size() - 1; j >= 0; --j) {
            auto TargetPage = FuncGVPage[j];
            auto OriginIndex = NextIndex;
            Value *GEP = IRB.CreateGEP(
              TargetPage->getValueType(), TargetPage,
              {Zero, NextIndex});
            NextIndex = IRB.CreateLoad(Int32Ty, GEP);
            if (opt.level() > 2) {
              NextIndex = IRB.CreateNeg(NextIndex);
            }
            if (opt.level() > 1) {
              NextIndex = IRB.CreateAdd(NextIndex, OriginIndex);
            }
            NextIndex = IRB.CreateXor(NextIndex, FuncKey);
            NextIndex = IRB.CreateCall(
              Intrinsic::getOrInsertDeclaration(&M, Intrinsic::fshl, {NextIndex->getType()}),
              {NextIndex, NextIndex, OriginIndex});
          }

          for (int j = GVPage.size() - 1; j >= 0; --j) {
            auto TargetPage = GVPage[j];
            auto OriginIndex = NextIndex;
            Value *GEP = IRB.CreateGEP(
              TargetPage->getValueType(), TargetPage,
              {Zero, NextIndex});
            if (j) {
              NextIndex = IRB.CreateLoad(Int32Ty, GEP);
              NextIndex = IRB.CreateSub(NextIndex, OriginIndex);
              NextIndex = IRB.CreateXor(NextIndex, ModuleKey);
              NextIndex = IRB.CreateCall(
                Intrinsic::getOrInsertDeclaration(&M, Intrinsic::fshr, {NextIndex->getType()}),
                {NextIndex, NextIndex, OriginIndex});
              continue;
            }

            Value *GVPtr = IRB.CreateLoad(
              PointerType::getUnqual(Ctx), GEP,
              GV->getName());
            GVPtr = IRB.CreateBitCast(GVPtr, GV->getType());
            Inst->replaceUsesOfWith(GV, GVPtr);
          }
          RunOnFuncChanged = true;
        }
      }
    }

    return true;
  }
  bool doFinalization(Module &M) override {
    if (!RunOnFuncChanged || GVPage.empty()) {
      return false;
    }
    for (auto gvPage : GVPage) {
      appendToCompilerUsed(M, {gvPage});
    }
    return true;
  }

  };
} // namespace llvm

char IndirectGlobalVariable::ID = 0;
FunctionPass *llvm::createIndirectGlobalVariablePass(unsigned pointerSize, ObfuscationOptions *argsOptions) {
  return new IndirectGlobalVariable(pointerSize, argsOptions);
}

INITIALIZE_PASS(IndirectGlobalVariable, "indgv", "Enable IR Indirect Global Variable Obfuscation", false, false)
