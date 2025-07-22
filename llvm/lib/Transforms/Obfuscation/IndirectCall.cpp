#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Obfuscation/IndirectCall.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/APInt.h"

#include <random>

#define DEBUG_TYPE "icall"

using namespace llvm;
namespace {
struct IndirectCall : public FunctionPass {
  static char ID;
  unsigned pointerSize;
  
  ObfuscationOptions *ArgsOptions;
  std::map<Function *, unsigned> CalleeIndex;
  std::vector<GlobalVariable *> CalleePage;
  std::map<Function *, std::vector<CallInst *>> FunctionCallSites;
  std::map<Function *, std::vector<Function *>> FunctionCallees;
  std::vector<Function *> Callees;
  CryptoUtils RandomEngine;
  std::map<Function *, Constant *> CalleeKeys;
  bool RunOnFuncChanged = false;

  IndirectCall(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  StringRef getPassName() const override { return {"IndirectCall"}; }

  void NumberCallees(Module &M) {
    auto Int32Ty = IntegerType::getInt32Ty(M.getContext());
    for (auto &F : M) {
      if (F.isIntrinsic()) {
        continue;
      }

      for (auto &BB : F) {
        for (auto &I : BB) {
          if (auto CI = dyn_cast<CallInst>(&I)) {
            auto CB = dyn_cast<CallBase>(&I);
            auto Callee = CB->getCalledFunction();
            if (Callee == nullptr) {
              Callee = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
              if (!Callee) {
                continue;
              }
            }
            if (Callee->isIntrinsic()) {
              continue;
            }
            FunctionCallSites[&F].push_back(CI);
            if (std::find(FunctionCallees[&F].begin(), FunctionCallees[&F].end(), Callee)
                == FunctionCallees[&F].end()) {
              FunctionCallees[&F].push_back(Callee);
            }
            if (CalleeIndex.count(Callee) == 0) {
              CalleeIndex[Callee] = {};
              Callees.push_back(Callee);
              CalleeKeys[Callee] = ConstantInt::get(Int32Ty, RandomEngine.get_uint32_t());
            }
          }
        }
      }
    }
  }

  bool doInitialization(Module &M) override {
    CalleeIndex.clear();
    FunctionCallSites.clear();
    FunctionCallees.clear();
    Callees.clear();
    CalleePage.clear();
    CalleeKeys.clear();
    auto Int32Ty = IntegerType::getInt32Ty(M.getContext());

    NumberCallees(M);
    if (!Callees.size()) {
      return false;
    }

    auto seed = RandomEngine.get_uint64_t();
    std::default_random_engine e(seed);
    std::shuffle(Callees.begin(), Callees.end(), e);

    std::vector<Constant *> GVCallees;
    for (unsigned i = 0; i < Callees.size(); ++i) {
      auto Callee = Callees[i];
      GVCallees.push_back(ConstantExpr::getBitCast(Callee, PointerType::getUnqual(M.getContext())));
      CalleeIndex[Callee] = i;
    }

    {
      std::string GVNameCallees(M.getName().str() + "_IndirectCallees");
      ArrayType *ATy = ArrayType::get(GVCallees[0]->getType(), GVCallees.size());
      Constant *CA = ConstantArray::get(ATy, ArrayRef(GVCallees));
      auto GV = new GlobalVariable(M, ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
        CA, GVNameCallees);
      CalleePage.push_back(GV);
    }

    for (unsigned i = 0; i < 1; ++i) {
      seed = RandomEngine.get_uint64_t();
      e = std::default_random_engine(seed);
      std::shuffle(Callees.begin(), Callees.end(), e);

      std::vector<Constant *> ConstantCalleeIndex;
      for (unsigned j = 0; j < Callees.size(); ++j) {
        auto Callee = Callees[j];
        APInt preIndex(32, CalleeIndex[Callee]);
        preIndex = preIndex.rotl(j).byteSwap();
        Constant *toWriteData = ConstantInt::get(Int32Ty, preIndex);
        toWriteData = ConstantExpr::getXor(toWriteData, CalleeKeys[Callee]);
        toWriteData = ConstantExpr::getAdd(toWriteData, ConstantInt::get(Int32Ty, j));
        ConstantCalleeIndex.push_back(toWriteData);
        CalleeIndex[Callee] = j;
      }

      {

        std::string GVNameCalleePage(M.getName().str() + "_IndirectCalleePage_" + std::to_string(i));
        auto IATy = ArrayType::get(Int32Ty, ConstantCalleeIndex.size());
        auto IA = ConstantArray::get(IATy, ArrayRef(ConstantCalleeIndex));
        auto GV = new GlobalVariable(M, IATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
          IA, GVNameCalleePage);
        CalleePage.push_back(GV);
      }
    }

    return false;
  }

  bool runOnFunction(Function &Fn) override {
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->iCallOpt(), &Fn);
    if (!opt.isEnabled()) {
      return false;
    }

    LLVMContext &Ctx = Fn.getContext();
    auto& M = *Fn.getParent();

    if (Callees.empty()) {
      return false;
    }
    const auto& CallSites = FunctionCallSites[&Fn];
    auto& FuncCallees = FunctionCallees[&Fn];

    if (CallSites.empty() || FuncCallees.empty()) {
      return false;
    }

    auto Int32Ty = IntegerType::getInt32Ty(Ctx);
    auto Zero = ConstantInt::getNullValue(Int32Ty);
    ConstantInt *FuncKey = ConstantInt::get(Int32Ty, RandomEngine.get_uint32_t());

    std::vector<GlobalVariable *> FuncCalleePage;
    std::map<Function *, unsigned> FuncCalleeIndex;
    for (unsigned i = 0; i < opt.level(); ++i) {
      auto seed = RandomEngine.get_uint64_t();
      auto e = std::default_random_engine(seed);
      std::shuffle(FuncCallees.begin(), FuncCallees.end(), e);

      std::vector<Constant *> ConstantCalleeIndex;
      for (unsigned j = 0; j < FuncCallees.size(); ++j) {
        auto Callee = FuncCallees[j];

        APInt preIndex(32, FuncCalleeIndex.find(Callee) == FuncCalleeIndex.end() ?
                             CalleeIndex[Callee] :
                             FuncCalleeIndex[Callee]);

        preIndex = preIndex.rotr(j);
        Constant *toWriteData = ConstantInt::get(Int32Ty, preIndex);
        toWriteData = ConstantExpr::getXor(toWriteData, FuncKey);
        if (opt.level() > 1) {
          toWriteData = ConstantExpr::getSub(toWriteData, ConstantInt::get(Int32Ty, j));
        }
        if (opt.level() > 2) {
          toWriteData = ConstantExpr::getNeg(toWriteData);
        }
        ConstantCalleeIndex.push_back(toWriteData);
        FuncCalleeIndex[Callee] = j;
      }

      {
        std::string GVNameCalleePage(M.getName().str() + "_" + Fn.getName().str() + "_IndirectCalleePage_" + std::to_string(i));
        auto IATy = ArrayType::get(Int32Ty, ConstantCalleeIndex.size());
        auto IA = ConstantArray::get(IATy, ArrayRef(ConstantCalleeIndex));
        auto GV = new GlobalVariable(M, IATy, false, GlobalValue::LinkageTypes::InternalLinkage,
          IA, GVNameCalleePage);
        FuncCalleePage.push_back(GV);
      }
    }

    for (auto CI : CallSites) {

      CallBase *CB = CI;

      Function *Callee = CB->getCalledFunction();
      if (Callee == nullptr) {
        Callee = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
        if (!Callee) {
          continue;
        }
      }
      IRBuilder<> IRB(CB);

      Value *NextIndex = FuncCalleeIndex.find(Callee) == FuncCalleeIndex.end() ?
                           ConstantInt::get(Int32Ty, CalleeIndex[Callee]) :
                           ConstantInt::get(Int32Ty, FuncCalleeIndex[Callee]) ;

      for (int i = FuncCalleePage.size() - 1; i >= 0; --i) {
        auto TargetPage = FuncCalleePage[i];
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

      for (int i = CalleePage.size() - 1; i >= 0; --i) {
        auto TargetPage = CalleePage[i];
        auto OriginIndex = NextIndex;
        Value *GEP = IRB.CreateGEP(
          TargetPage->getValueType(), TargetPage,
          {Zero, NextIndex});
        if (i) {
          NextIndex = IRB.CreateLoad(Int32Ty, GEP);
          NextIndex = IRB.CreateSub(NextIndex, OriginIndex);
          NextIndex = IRB.CreateXor(NextIndex, CalleeKeys[Callee]);
          NextIndex = IRB.CreateCall(
              Intrinsic::getOrInsertDeclaration(&M, Intrinsic::bswap, {NextIndex->getType()}),
              {NextIndex});

          NextIndex = IRB.CreateCall(
              Intrinsic::getOrInsertDeclaration(&M, Intrinsic::fshr, {NextIndex->getType()}),
              {NextIndex, NextIndex, OriginIndex});
          continue;
        }

        Value *FnPtr = IRB.CreateLoad(
          Callee->getType(), GEP,
          CI->getName());
        FnPtr->setName("Call_" + Callee->getName());
        CB->setCalledOperand(FnPtr);
      }
    }

    RunOnFuncChanged = true;
    return true;
  }

  bool doFinalization(Module & M) override {
    if (!RunOnFuncChanged || CalleePage.empty()) {
      return false;
    }
    for (auto calleePage : CalleePage) {
      appendToCompilerUsed(M, {calleePage});
    }
    return true;
  }

};
} // namespace llvm

char IndirectCall::ID = 0;
FunctionPass *llvm::createIndirectCallPass(unsigned pointerSize, ObfuscationOptions *argsOptions) {
  return new IndirectCall(pointerSize, argsOptions);
}

INITIALIZE_PASS(IndirectCall, "icall", "Enable IR Indirect Call Obfuscation", false, false)
