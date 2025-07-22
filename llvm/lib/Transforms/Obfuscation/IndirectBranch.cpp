#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Obfuscation/IndirectBranch.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/Module.h"

#include <random>

#define DEBUG_TYPE "indbr"

using namespace llvm;
namespace {
struct IndirectBranch : public FunctionPass {
  unsigned pointerSize;
  static char ID;
  
  ObfuscationOptions *ArgsOptions;
  std::map<BasicBlock *, unsigned> BBIndex;
  std::vector<GlobalVariable *> BBPage;
  std::map<Function *, std::vector<BasicBlock *>> FunctionBBs;
  std::map<Function *, std::vector<BranchInst *>> FunctionBrs;
  std::vector<BasicBlock *> BBTargets;        //all conditional branch targets
  CryptoUtils RandomEngine;
  Constant *ModuleKey = nullptr;
  bool RunOnFuncChanged = false;

  IndirectBranch(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  StringRef getPassName() const override { return {"IndirectBranch"}; }

  void NumberBasicBlock(Module &M) {
    for (auto &F : M) {
      if (F.empty() || F.hasLinkOnceLinkage() || F.getSection() == ".text.startup") {
        continue;
      }
      SplitAllCriticalEdges(F, CriticalEdgeSplittingOptions(nullptr, nullptr));
      for (auto &BB : F) {
        if (auto *BI = dyn_cast<BranchInst>(BB.getTerminator())) {
          if (BI->isConditional()) {
            FunctionBrs[&F].push_back(BI);
            unsigned N = BI->getNumSuccessors();
            for (unsigned I = 0; I < N; I++) {
              BasicBlock *Succ = BI->getSuccessor(I);
              if (std::find(FunctionBBs[&F].begin(), FunctionBBs[&F].end(), Succ)
                  == FunctionBBs[&F].end()) {
                FunctionBBs[&F].push_back(Succ);
              }
              if (BBIndex.count(Succ) == 0) {
                BBTargets.push_back(Succ);
                BBIndex[Succ] = 0;
              }
            }
          }
        }
      }
    }
  }

  bool doInitialization(Module &M) override {
    BBIndex.clear();
    BBPage.clear();
    FunctionBBs.clear();
    FunctionBrs.clear();
    BBTargets.clear();

    auto Int32Ty = IntegerType::getInt32Ty(M.getContext());
    ModuleKey = ConstantInt::get(Int32Ty, RandomEngine.get_uint32_t());
    NumberBasicBlock(M);
    if (BBTargets.empty()) {
      return false;
    }

    auto seed = RandomEngine.get_uint64_t();
    std::default_random_engine e(seed);
    std::shuffle(BBTargets.begin(), BBTargets.end(), e);

    std::vector<Constant *> GVBBs;
    for (unsigned i = 0; i < BBTargets.size(); ++i) {
      auto BB = BBTargets[i];
      GVBBs.push_back(ConstantExpr::getBitCast(BlockAddress::get(BB), PointerType::getUnqual(M.getContext())));
      BBIndex[BB] = i;
    }

    {
      std::string GVNameBBs(M.getName().str() + "_IndirectBBs");
      ArrayType *ATy = ArrayType::get(GVBBs[0]->getType(), GVBBs.size());
      Constant *CA = ConstantArray::get(ATy, ArrayRef(GVBBs));
      auto GV = new GlobalVariable(M, ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
                                   CA, GVNameBBs);
      BBPage.push_back(GV);
    }

    for (unsigned i = 0; i < 1; ++i) {
      seed = RandomEngine.get_uint64_t();
      e = std::default_random_engine(seed);
      std::shuffle(BBTargets.begin(), BBTargets.end(), e);

      std::vector<Constant *> ConstantBBIndex;
      for (unsigned j = 0; j < BBTargets.size(); ++j) {
        auto BB = BBTargets[j];
        APInt preIndex(32, BBIndex[BB]);
        preIndex = preIndex.rotl(j).byteSwap();
        Constant *toWriteData = ConstantInt::get(Int32Ty, preIndex);
        toWriteData = ConstantExpr::getXor(toWriteData, ModuleKey);
        toWriteData = ConstantExpr::getAdd(toWriteData, ConstantInt::get(Int32Ty, j));
        ConstantBBIndex.push_back(toWriteData);
        BBIndex[BB] = j;
      }

      {

        std::string GVNameBBPage(M.getName().str() + "_IndirectBBPage_" + std::to_string(i));
        auto IATy = ArrayType::get(Int32Ty, ConstantBBIndex.size());
        auto IA = ConstantArray::get(IATy, ArrayRef(ConstantBBIndex));
        auto GV = new GlobalVariable(M, IATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
          IA, GVNameBBPage);
        BBPage.push_back(GV);
      }
    }

    return false;
  }


  bool runOnFunction(Function &Fn) override {
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->indBrOpt(), &Fn);
    if (!opt.isEnabled()) {
      return false;
    }

    LLVMContext &Ctx = Fn.getContext();
    auto& M = *Fn.getParent();

    if (BBTargets.empty()) {
      return false;
    }


    auto& FuncBBs = FunctionBBs[&Fn];
    auto& FuncBrs = FunctionBrs[&Fn];
    if (FuncBBs.empty() || FuncBrs.empty()) {
      return false;
    }

    auto Int32Ty = IntegerType::getInt32Ty(Ctx);
    auto Zero = ConstantInt::getNullValue(Int32Ty);
    ConstantInt *FuncKey = ConstantInt::get(Int32Ty, RandomEngine.get_uint32_t());

    std::vector<GlobalVariable *> FuncBBPage;
    std::map<BasicBlock *, unsigned> FuncBBIndex;
    for (unsigned i = 0; i < opt.level(); ++i) {
      auto seed = RandomEngine.get_uint64_t();
      auto e = std::default_random_engine(seed);
      std::shuffle(FuncBBs.begin(), FuncBBs.end(), e);

      std::vector<Constant *> ConstantBBIndex;
      for (unsigned j = 0; j < FuncBBs.size(); ++j) {
        auto BB = FuncBBs[j];

        APInt preIndex(32, FuncBBIndex.find(BB) == FuncBBIndex.end() ?
                             BBIndex[BB] :
                             FuncBBIndex[BB]);

        preIndex = preIndex.rotr(j);
        Constant *toWriteData = ConstantInt::get(Int32Ty, preIndex);
        toWriteData = ConstantExpr::getXor(toWriteData, FuncKey);
        if (opt.level() > 1) {
          toWriteData = ConstantExpr::getSub(toWriteData, ConstantInt::get(Int32Ty, j));
        }
        if (opt.level() > 2) {
          toWriteData = ConstantExpr::getNeg(toWriteData);
        }
        ConstantBBIndex.push_back(toWriteData);
        FuncBBIndex[BB] = j;
      }

      {
        std::string GVNameBBPage(M.getName().str() + "_" + Fn.getName().str() + "_IndirectBBPage_" + std::to_string(i));
        auto IATy = ArrayType::get(Int32Ty, ConstantBBIndex.size());
        auto IA = ConstantArray::get(IATy, ArrayRef(ConstantBBIndex));
        auto GV = new GlobalVariable(M, IATy, false, GlobalValue::LinkageTypes::InternalLinkage,
          IA, GVNameBBPage);
        FuncBBPage.push_back(GV);
      }
    }

    for (auto &BI : FuncBrs) {
      if (BI && BI->isConditional()) {
        IRBuilder<> IRB(BI);

        auto Cond = BI->getCondition();
        auto TBB = BI->getSuccessor(0);
        auto FBB = BI->getSuccessor(1);

        auto TIndex = FuncBBIndex.find(TBB) == FuncBBIndex.end() ?
          ConstantInt::get(Int32Ty, BBIndex[TBB]) :
          ConstantInt::get(Int32Ty, FuncBBIndex[TBB]) ;

        auto FIndex = FuncBBIndex.find(FBB) == FuncBBIndex.end() ?
          ConstantInt::get(Int32Ty, BBIndex[FBB]) :
          ConstantInt::get(Int32Ty, FuncBBIndex[FBB]) ;

        auto NextIndex = IRB.CreateSelect(Cond, TIndex, FIndex);
        for (int j = FuncBBPage.size() - 1; j >= 0; --j) {
          auto TargetPage = FuncBBPage[j];
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

        for (int j = BBPage.size() - 1; j >= 0; --j) {
          auto TargetPage = BBPage[j];
          auto OriginIndex = NextIndex;
          Value *GEP = IRB.CreateGEP(
            TargetPage->getValueType(), TargetPage,
            {Zero, NextIndex});
          if (j) {
            NextIndex = IRB.CreateLoad(Int32Ty, GEP);
            NextIndex = IRB.CreateSub(NextIndex, OriginIndex);
            NextIndex = IRB.CreateXor(NextIndex, ModuleKey);
            NextIndex = IRB.CreateCall(
              Intrinsic::getOrInsertDeclaration(&M, Intrinsic::bswap, {NextIndex->getType()}),
              {NextIndex});

            NextIndex = IRB.CreateCall(
              Intrinsic::getOrInsertDeclaration(&M, Intrinsic::fshr, {NextIndex->getType()}),
              {NextIndex, NextIndex, OriginIndex});
            continue;
          }

          Value *BBPtr = IRB.CreateLoad(
              PointerType::getUnqual(Ctx), GEP);
          IndirectBrInst *IBI = IndirectBrInst::Create(BBPtr, 2);
          IBI->addDestination(BI->getSuccessor(0));
          IBI->addDestination(BI->getSuccessor(1));
          ReplaceInstWithInst(BI, IBI);
        }
        RunOnFuncChanged = true;
      }
    }

    return true;
  }

  bool doFinalization(Module &M) override {
    if (!RunOnFuncChanged || BBPage.empty()) {
      return false;
    }
    for (auto bbPage : BBPage) {
      appendToCompilerUsed(M, {bbPage});
    }
    return true;
  }

};
} // namespace llvm

char IndirectBranch::ID = 0;
FunctionPass *llvm::createIndirectBranchPass(unsigned pointerSize, ObfuscationOptions *argsOptions) {
  return new IndirectBranch(pointerSize, argsOptions);
}
INITIALIZE_PASS(IndirectBranch, "indbr", "Enable IR Indirect Branch Obfuscation", false, false)
