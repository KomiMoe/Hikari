#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/ConstantIntEncryption.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Utils/GlobalStatus.h"
#include "llvm/Transforms/IPO/Attributor.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/CryptoUtils.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <map>
#include <set>
#include <iostream>
#include <algorithm>

#define DEBUG_TYPE "constant-int-encryption"

using namespace llvm;

namespace {

struct ConstantIntEncryption : public FunctionPass {
  static char         ID;
  ObfuscationOptions *ArgsOptions;

  std::unordered_map<Function *, std::set<Instruction *>> FunctionModifyIRs;

  CryptoUtils         RandomEngine;

  ConstantIntEncryption(ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->ArgsOptions = argsOptions;
  }

  StringRef getPassName() const override {
    return "ConstantIntEncryption";
  }

  bool doInitialization(Module &M) override {
    bool Changed = false;
    for (auto& F : M) {
      const auto opt = ArgsOptions->toObfuscate(ArgsOptions->cieOpt(), &F);
      if (!opt.isEnabled()) {
        continue;
      }
      Changed |= expandConstantExpr(F);
      for (auto& BB : F) {
        for (auto& I : BB) {
          if (I.isEHPad() || isa<AllocaInst>(&I) ||
              isa<IntrinsicInst>(&I) || isa<SwitchInst>(I)||
              I.isAtomic()) {
            continue;
          }
          auto CI = dyn_cast<CallInst>(&I);
          auto GEP = dyn_cast<GetElementPtrInst>(&I);
          auto PHI = dyn_cast<PHINode>(&I);

          for (unsigned i = 0; i < (PHI ? PHI->getNumIncomingValues() : I.getNumOperands()); ++i) {
            if (CI && CI->isBundleOperand(i)) {
              continue;
            }
            if (GEP && (i < 2 || GEP->getSourceElementType()->isStructTy())) {
              continue;
            }
            if (PHI && isa<SwitchInst>(PHI->getIncomingBlock(i)->getTerminator())) {
              continue;
            }
            Value* Opr = PHI ? PHI->getIncomingValue(i) : I.getOperand(i);
            auto CTI = dyn_cast<ConstantInt>(Opr);
            if (CTI && CTI->getBitWidth() > 7) {
              FunctionModifyIRs[&F].emplace(&I);
              break;
            }
          }
        }
      }
    }
    return Changed;
  }

  bool runOnFunction(Function &F) override {
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->cieOpt(), &F);
    if (!opt.isEnabled()) {
      return false;
    }
    auto& FuncModifyIRs = FunctionModifyIRs[&F];
    if (FunctionModifyIRs.empty()) {
      return false;
    }

    for (auto I : FuncModifyIRs) {
      auto CI = dyn_cast<CallInst>(I);
      auto GEP = dyn_cast<GetElementPtrInst>(I);
      auto PHI = dyn_cast<PHINode>(I);

      for (unsigned i = 0; i < I->getNumOperands(); ++i) {
        if (CI && CI->isBundleOperand(i)) {
          continue;
        }
        if (GEP && i < 2) {
          continue;
        }
        Value* Opr = I->getOperand(i);
        if (auto CTI = dyn_cast<ConstantInt>(Opr)) {
          if (CTI->getBitWidth() < 4) {
            continue;
          }
          if (PHI && isa<SwitchInst>(PHI->getIncomingBlock(i)->getTerminator())) {
            continue;
          }

          auto InsertPoint = PHI ?
                               PHI->getIncomingBlock(i)->getTerminator() :
                               I;
          auto CipherConstant = encryptConstant(CTI, InsertPoint, &RandomEngine, opt.level());
          if (PHI)
            PHI->setIncomingValue(i, CipherConstant);
          else
            I->setOperand(i, CipherConstant);
        }
      }
    }
    return true;
  }
};
} // namespace llvm

char ConstantIntEncryption::ID = 0;

FunctionPass *llvm::createConstantIntEncryptionPass(
    ObfuscationOptions *argsOptions) {
  return new ConstantIntEncryption(argsOptions);
}

INITIALIZE_PASS(ConstantIntEncryption, "cie",
                "Enable IR Constant Integer Encryption", false, false)