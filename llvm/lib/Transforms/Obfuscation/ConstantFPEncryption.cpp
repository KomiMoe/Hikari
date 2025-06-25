#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/ConstantFPEncryption.h"
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

#define DEBUG_TYPE "constant-fp-encryption"

using namespace llvm;

namespace {

struct ConstantFPEncryption : public FunctionPass {
  static char         ID;
  ObfuscationOptions *ArgsOptions;
  CryptoUtils         RandomEngine;

  ConstantFPEncryption(ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->ArgsOptions = argsOptions;
  }

  StringRef getPassName() const override {
    return {"ConstantFPEncryption"};
  }

  Value *createConstantFPEncrypt0(BasicBlock::iterator ip, ConstantFP *CFP) {
    const auto  Module = ip->getModule();
    auto &LLVMContent = Module->getContext();

    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);
    const auto FPWidth = CFP->getType()->getPrimitiveSizeInBits().
                              getFixedValue();


    const auto Key = ConstantInt::get(
        IntegerType::get(LLVMContent, FPWidth),
        RandomEngine.get_uint64_t());

    const auto FPInt = ConstantExpr::getBitCast(CFP, Key->getType());

    const auto Enc = ConstantExpr::getSub(FPInt, Key);
    auto       GV = new GlobalVariable(*Module, Enc->getType(), false,
                                       GlobalValue::LinkageTypes::PrivateLinkage,
                                       Enc);

    appendToCompilerUsed(*Module, {GV});
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto Add = IRB.CreateAdd(Key, Load);
    const auto NewOpr = IRB.CreateBitCast(Add, CFP->getType());
    return NewOpr;
  }

  Value *createConstantFPEncrypt1(BasicBlock::iterator ip, ConstantFP *CFP) {
    const auto  Module = ip->getModule();
    auto &LLVMContent = Module->getContext();

    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);
    const auto FPWidth = CFP->getType()->getPrimitiveSizeInBits().
      getFixedValue();


    const auto Key = ConstantInt::get(
      IntegerType::get(LLVMContent, FPWidth),
      RandomEngine.get_uint64_t());

    const auto XorKey = ConstantInt::get(Key->getType(),
      RandomEngine.get_uint64_t());


    const auto FPInt = ConstantExpr::getBitCast(CFP, Key->getType());

    auto Enc = ConstantExpr::getSub(FPInt, Key);
    Enc = ConstantExpr::getXor(Enc, XorKey);

    auto       GV = new GlobalVariable(*Module, Enc->getType(), false,
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
    const auto Add = IRB.CreateAdd(Key, XorOpr);
    const auto NewOpr = IRB.CreateBitCast(Add, CFP->getType());
    return NewOpr;
  }

  Value *createConstantFPEncrypt2(BasicBlock::iterator ip, ConstantFP *CFP) {
    const auto  Module = ip->getModule();
    auto &LLVMContent = Module->getContext();

    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);
    const auto FPWidth = CFP->getType()->getPrimitiveSizeInBits().
      getFixedValue();


    const auto Key = ConstantInt::get(
      IntegerType::get(LLVMContent, FPWidth),
      RandomEngine.get_uint64_t());

    const auto XorKey = ConstantInt::get(Key->getType(),
      RandomEngine.get_uint64_t());
    const auto MulXorKey = ConstantExpr::getMul(Key, XorKey);

    const auto FPInt = ConstantExpr::getBitCast(CFP, Key->getType());

    auto Enc = ConstantExpr::getSub(FPInt, Key);
    Enc = ConstantExpr::getXor(Enc, MulXorKey);

    auto       GV = new GlobalVariable(*Module, Enc->getType(), false,
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
    const auto Add = IRB.CreateAdd(Key, XorOpr);
    const auto NewOpr = IRB.CreateBitCast(Add, CFP->getType());
    return NewOpr;
  }

  Value *createConstantFPEncrypt3(BasicBlock::iterator ip, ConstantFP *CFP) {
    const auto  Module = ip->getModule();
    auto &LLVMContent = Module->getContext();

    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);
    const auto FPWidth = CFP->getType()->getPrimitiveSizeInBits().
      getFixedValue();


    const auto Key = ConstantInt::get(
      IntegerType::get(LLVMContent, FPWidth),
      RandomEngine.get_uint64_t());

    auto XorKey = ConstantInt::get(Key->getType(),
      RandomEngine.get_uint64_t());
    const auto MulXorKey = ConstantExpr::getMul(Key, XorKey);

    const auto FPInt = ConstantExpr::getBitCast(CFP, Key->getType());

    auto Enc = ConstantExpr::getSub(FPInt, Key);
    Enc = ConstantExpr::getXor(Enc, MulXorKey);

    XorKey = ConstantExpr::getNeg(XorKey);
    XorKey = ConstantExpr::getXor(XorKey, Enc);
    XorKey = ConstantExpr::getNeg(XorKey);

    auto       GV = new GlobalVariable(*Module, Enc->getType(), false,
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
    const auto Add = IRB.CreateAdd(Key, XorOpr);
    const auto NewOpr = IRB.CreateBitCast(Add, CFP->getType());
    return NewOpr;
  }

  bool runOnFunction(Function &F) override {
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->cfeOpt(), &F);
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
          if (auto CFP = dyn_cast<ConstantFP>(Opr)) {
            Value *NewOpr;
            if (opt.level() == 0) {
              NewOpr = createConstantFPEncrypt0(InsertPt, CFP);
            } else if (opt.level() == 1) {
              NewOpr = createConstantFPEncrypt1(InsertPt, CFP);
            } else if (opt.level() == 2) {
              NewOpr = createConstantFPEncrypt2(InsertPt, CFP);
            } else {
              NewOpr = createConstantFPEncrypt3(InsertPt, CFP);
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

char ConstantFPEncryption::ID = 0;

FunctionPass *llvm::createConstantFPEncryptionPass(
    ObfuscationOptions *argsOptions) {
  return new ConstantFPEncryption(argsOptions);
}

INITIALIZE_PASS(ConstantFPEncryption, "cfe",
                "Enable IR Constant FP Encryption", false, false)