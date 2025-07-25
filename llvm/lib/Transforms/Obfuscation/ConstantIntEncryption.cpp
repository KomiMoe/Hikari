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
  CryptoUtils         RandomEngine;

  ConstantIntEncryption(ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->ArgsOptions = argsOptions;
  }

  Value *createConstantIntEncrypt0(BasicBlock::iterator ip, ConstantInt *CIT) {
  StringRef getPassName() const override {
    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    const auto Key = ConstantInt::get(CIT->getType(),
                                      RandomEngine.get_uint64_t());
    const auto Enc = ConstantExpr::getSub(CIT, Key);
    auto       GV = new GlobalVariable(*Module, Enc->getType(), false,
                                       GlobalValue::LinkageTypes::PrivateLinkage,
                                       Enc);
    appendToCompilerUsed(*Module, {GV});
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto NewOpr = IRB.CreateAdd(Key, Load);
    return NewOpr;
  }

  Value *createConstantIntEncrypt1(BasicBlock::iterator ip, ConstantInt *CIT) {
    const auto          Module = ip->getModule();
    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    const auto Key = ConstantInt::get(CIT->getType(),
                                      RandomEngine.get_uint64_t());
    const auto XorKey = ConstantInt::get(CIT->getType(),
                                         RandomEngine.get_uint64_t());

    auto Enc = ConstantExpr::getSub(CIT, Key);
    Enc = ConstantExpr::getXor(Enc, XorKey);

    auto GV = new GlobalVariable(*Module, Enc->getType(), false,
                                 GlobalValue::LinkageTypes::PrivateLinkage,
                                 Enc);
    appendToCompilerUsed(*Module, {GV});

    auto GXorKey = new GlobalVariable(*Module, XorKey->getType(), false,
                                      GlobalValue::LinkageTypes::PrivateLinkage,
                                      XorKey);
    appendToCompilerUsed(*Module, {GXorKey});

    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto LoadXor = IRB.CreateLoad(XorKey->getType(), GXorKey);
    const auto XorOpr = IRB.CreateXor(Load, LoadXor);
    const auto NewOpr = IRB.CreateAdd(Key, XorOpr);
    return NewOpr;
  }

  Value *createConstantIntEncrypt2(BasicBlock::iterator ip, ConstantInt *CIT) {
    const auto          Module = ip->getModule();
    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    const auto Key = ConstantInt::get(CIT->getType(),
                                      RandomEngine.get_uint64_t());
    const auto XorKey = ConstantInt::get(CIT->getType(),
                                         RandomEngine.get_uint64_t());

    const auto MulXorKey = ConstantExpr::getMul(Key, XorKey);

    auto Enc = ConstantExpr::getSub(CIT, Key);
    Enc = ConstantExpr::getXor(Enc, MulXorKey);

    auto GV = new GlobalVariable(*Module, Enc->getType(), false,
                                 GlobalValue::LinkageTypes::PrivateLinkage,
                                 Enc);
    appendToCompilerUsed(*Module, {GV});

    auto GXorKey = new GlobalVariable(*Module, XorKey->getType(), false,
                                      GlobalValue::LinkageTypes::PrivateLinkage,
                                      XorKey);
    appendToCompilerUsed(*Module, {GXorKey});

    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto LoadXor = IRB.CreateLoad(XorKey->getType(), GXorKey);
    const auto MulOpr = IRB.CreateMul(Key, LoadXor);
    const auto XorOpr = IRB.CreateXor(Load, MulOpr);
    const auto NewOpr = IRB.CreateAdd(Key, XorOpr);
    return NewOpr;
  }

  Value *createConstantIntEncrypt3(BasicBlock::iterator ip, ConstantInt *CIT) {
    const auto          Module = ip->getModule();
    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    const auto Key = ConstantInt::get(CIT->getType(),
                                      RandomEngine.get_uint64_t());
    auto XorKey = ConstantInt::get(CIT->getType(),
                                         RandomEngine.get_uint64_t());

    const auto MulXorKey = ConstantExpr::getMul(Key, XorKey);

    auto Enc = ConstantExpr::getSub(CIT, Key);
    Enc = ConstantExpr::getXor(Enc, MulXorKey);

    XorKey = ConstantExpr::getNeg(XorKey);
    XorKey = ConstantExpr::getXor(XorKey, Enc);
    XorKey = ConstantExpr::getNeg(XorKey);

    auto GV = new GlobalVariable(*Module, Enc->getType(), false,
                                 GlobalValue::LinkageTypes::PrivateLinkage,
                                 Enc);
    appendToCompilerUsed(*Module, {GV});

    auto GXorKey = new GlobalVariable(*Module, XorKey->getType(), false,
                                      GlobalValue::LinkageTypes::PrivateLinkage,
                                      XorKey);
    appendToCompilerUsed(*Module, {GXorKey});

    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto LoadXor = IRB.CreateLoad(XorKey->getType(), GXorKey);
    const auto XorKeyNegOpr = IRB.CreateNeg(LoadXor);
    const auto XorKeyXorEnc = IRB.CreateXor(XorKeyNegOpr, Load);
    const auto FinalXor = IRB.CreateNeg(XorKeyXorEnc);

    const auto MulOpr = IRB.CreateMul(Key, FinalXor);
    const auto XorOpr = IRB.CreateXor(Load, MulOpr);
    const auto NewOpr = IRB.CreateAdd(Key, XorOpr);
    return NewOpr;
  }

  bool runOnFunction(Function &F) override {
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->cieOpt(), &F);
    if (!opt.isEnabled()) {
      return false;
    }

    bool Changed = expandConstantExpr(F);

    for (auto &BB : F) {
      for (auto &I : BB) {
        if (I.isEHPad() || isa<AllocaInst>(&I) || isa<IntrinsicInst>(&I) ||
            isa<SwitchInst>(&I) || I.isAtomic()) {
          continue;
        }
        auto CI = dyn_cast<CallInst>(&I);
        auto GEP = dyn_cast<GetElementPtrInst>(&I);
        auto IsPhi = isa<PHINode>(&I);
        auto InsertPt = IsPhi
                          ? F.getEntryBlock().getFirstInsertionPt()
                          : I.getIterator();

        for (unsigned i = 0; i < I.getNumOperands(); ++i) {
          if (CI && CI->isBundleOperand(i)) {
            continue;
          }
          if (GEP && (i < 2 || GEP->getSourceElementType()->isStructTy())) {
            continue;
          }
          auto Opr = I.getOperand(i);
          if (auto CIT = dyn_cast<ConstantInt>(Opr)) {
            Value *NewOpr;
            if (opt.level() == 0) {
              NewOpr = createConstantIntEncrypt0(InsertPt, CIT);
            } else if (opt.level() == 1) {
              NewOpr = createConstantIntEncrypt1(InsertPt, CIT);
            } else if (opt.level() == 2) {
              NewOpr = createConstantIntEncrypt2(InsertPt, CIT);
            } else {
              NewOpr = createConstantIntEncrypt3(InsertPt, CIT);
            }

            I.setOperand(i, NewOpr);
            // outs() << I << "\n\n";
            Changed = true;
          }
        }

      }
    }
    return Changed;
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