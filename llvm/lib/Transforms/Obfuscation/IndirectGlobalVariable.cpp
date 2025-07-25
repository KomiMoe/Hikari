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

  std::unordered_map<Function *, std::set<GlobalVariable *>> FunctionGVs;

  std::vector<Constant *> GlobalVariables;
  std::unordered_map<Constant *, unsigned> GVIndex;
  std::unordered_map<Constant *, uint64_t> GVKeys;
  std::vector<GlobalVariable *> GVPageTable;

  CryptoUtils RandomEngine;
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
      LowerConstantExpr(F);
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
            if (GV->getMetadata("noobf")) {
              continue;
            }

            FunctionGVs[&F].emplace(GV);
            if (GVKeys.count(GV) == 0) {
              GlobalVariables.push_back(GV);
              GVKeys[GV] = RandomEngine.get_uint64_t();
            }
          }
        }
      }
    }
  }

  bool doInitialization(Module &M) override {
    GVIndex.clear();
    GVPageTable.clear();
    FunctionGVs.clear();
    GlobalVariables.clear();
    GVKeys.clear();

    NumberGlobalVariable(M);
    if (GlobalVariables.empty()) {
      return false;
    }

    CreatePageTableArgs createPageTableArgs;
    createPageTableArgs.CountLoop = 1;
    createPageTableArgs.GVNamePrefix = M.getName().str() + "_IndirectGVs" ;
    createPageTableArgs.RandomEngine = &RandomEngine;
    createPageTableArgs.M = &M;
    createPageTableArgs.Objects = &GlobalVariables;
    createPageTableArgs.IndexMap = &GVIndex;
    createPageTableArgs.ObjectKeys = &GVKeys;
    createPageTableArgs.OutPageTable = &GVPageTable;

    createPageTable(createPageTableArgs);
    return false;
  }


  bool runOnFunction(Function &Fn) override {
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->indGvOpt(), &Fn);
    if (!opt.isEnabled()) {
      return false;
    }

    auto& M = *Fn.getParent();

    if (GlobalVariables.empty()) {
      return false;
    }

    auto& FuncGVSet = FunctionGVs[&Fn];
    if (FuncGVSet.empty()) {
      return false;
    }

    std::vector<Constant *> FuncGVs;
    std::unordered_map<Constant *, uint64_t> FuncKeys;
    for (auto GV : FuncGVSet) {
      FuncGVs.push_back(GV);
      FuncKeys[GV] = RandomEngine.get_uint64_t();
    }

    std::vector<GlobalVariable *> FuncGVPageTable;
    std::unordered_map<Constant *, unsigned> FuncGVIndex;

    if (opt.level()) {
      CreatePageTableArgs createPageTableArgs;
      createPageTableArgs.CountLoop = opt.level();
      createPageTableArgs.GVNamePrefix = M.getName().str() + Fn.getName().str() + "_IndirectGVs" ;
      createPageTableArgs.RandomEngine = &RandomEngine;
      createPageTableArgs.M = &M;
      createPageTableArgs.Objects = &FuncGVs;
      createPageTableArgs.IndexMap = &GVIndex;
      createPageTableArgs.ObjectKeys = &FuncKeys;
      createPageTableArgs.OutPageTable = &FuncGVPageTable;

      enhancedPageTable(createPageTableArgs, &FuncGVIndex);
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

          auto PHI = dyn_cast<PHINode>(Inst);
          auto InsertPoint = PHI ? PHI->getIncomingBlock(i)->getTerminator() : Inst;
          IRBuilder<> IRB(InsertPoint);

          BuildDecryptArgs buildDecrypt;
          buildDecrypt.FuncLoopCount = opt.level();
          buildDecrypt.NextIndex = opt.level() ?
                                     FuncGVIndex[GV] :
                                     GVIndex[GV];
          buildDecrypt.NextIndexValue = nullptr;
          buildDecrypt.Fn = &Fn;
          buildDecrypt.InsertBefore = InsertPoint;
          buildDecrypt.LoadTy = GV->getType();
          buildDecrypt.ModulePageTable = &GVPageTable;
          buildDecrypt.FuncPageTable = &FuncGVPageTable;
          buildDecrypt.ModuleKey = GVKeys[GV];
          buildDecrypt.FuncKey = FuncKeys[GV];

          auto GVPtr = buildPageTableDecryptIR(buildDecrypt);
          if (PHI)
            PHI->setIncomingValue(i, GVPtr);
          else
            Inst->replaceUsesOfWith(GV, GVPtr);
          RunOnFuncChanged = true;
        }
      }
    }

    return true;
  }
  bool doFinalization(Module &M) override {
    if (!RunOnFuncChanged || GVPageTable.empty()) {
      return false;
    }
    for (auto gvPage : GVPageTable) {
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
