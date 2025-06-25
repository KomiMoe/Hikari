#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Obfuscation/IndirectCall.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/Module.h"

#include <random>

#define DEBUG_TYPE "icall"

using namespace llvm;
namespace {
struct IndirectCall : public FunctionPass {
  static char ID;
  unsigned pointerSize;
  
  ObfuscationOptions *ArgsOptions;
  std::map<Function *, unsigned> CalleeNumbering;
  std::vector<CallInst *> CallSites;
  std::vector<Function *> Callees;
  CryptoUtils RandomEngine;

  IndirectCall(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  StringRef getPassName() const override { return {"IndirectCall"}; }

  void NumberCallees(Function &F) {
    for (auto &BB:F) {
      for (auto &I:BB) {
        if (dyn_cast<CallInst>(&I)) {
          CallBase *CB = dyn_cast<CallBase>(&I);
          Function *Callee = CB->getCalledFunction();
          if (Callee == nullptr) {
            continue;
          }
          if (Callee->isIntrinsic()) {
            continue;
          }
          CallSites.push_back((CallInst *) &I);
          if (CalleeNumbering.count(Callee) == 0) {
            CalleeNumbering[Callee] = 0;
            Callees.push_back(Callee);
          }
        }
      }
    }

    long seed = RandomEngine.get_uint32_t();
    std::default_random_engine e(seed);
    std::shuffle(Callees.begin(), Callees.end(), e);
    unsigned N = 0;
    for (auto Callee:Callees) {
      CalleeNumbering[Callee] = N++;
    }
  }

  GlobalVariable *getIndirectCallees0(Function &F, ConstantInt *EncKey) const {
    std::string GVName(F.getName().str() + "_IndirectCallees");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    // callee's address
    std::vector<Constant *> Elements;
    for (auto Callee:Callees) {
      Constant *CE = ConstantExpr::getBitCast(
          Callee, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, EncKey);
      Elements.push_back(CE);
    }

    ArrayType *ATy =
        ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));
    GV = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
                                               CA, GVName);
    appendToCompilerUsed(*F.getParent(), {GV});
    return GV;
  }

  GlobalVariable *getIndirectCallees1(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) const {
    std::string GVName(F.getName().str() + "_IndirectCallees1");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    // callee's address
    std::vector<Constant *> Elements;
    for (auto Callee:Callees) {
      Constant *CE = ConstantExpr::getBitCast(
        Callee, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, XorKey));
      Elements.push_back(CE);
    }

    ArrayType *ATy =
      ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));
    GV = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
      CA, GVName);
    appendToCompilerUsed(*F.getParent(), {GV});
    return GV;
  }

  GlobalVariable * getIndirectCallees2(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) {
    std::string GVName(F.getName().str() + "_IndirectCallees2");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;


    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    // callee's address
    std::vector<Constant *> Elements;
    for (auto Callee:Callees) {
      Constant *CE = ConstantExpr::getBitCast(
        Callee, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, CalleeNumbering[Callee], false))));
      Elements.push_back(CE);
    }

    ArrayType *ATy =
      ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));
    GV = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
      CA, GVName);
    appendToCompilerUsed(*F.getParent(), {GV});
    
    return GV;
  }

  std::pair<GlobalVariable *, GlobalVariable *> getIndirectCallees3(Function &F, ConstantInt *AddKey) {
    std::string GVNameAdd(F.getName().str() + "_IndirectCallees3_Add");
    std::string GVNameXor(F.getName().str() + "_IndirectCallees3_Xor");
    GlobalVariable *GVAdd = F.getParent()->getNamedGlobal(GVNameAdd);
    GlobalVariable *GVXor = F.getParent()->getNamedGlobal(GVNameXor);
    if (GVAdd && GVXor)
      return std::make_pair(GVAdd, GVXor);


    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    // callee's address
    std::vector<Constant *> Elements;
    std::vector<Constant *> XorKeys;
    for (auto Callee:Callees) {
      uint64_t V = RandomEngine.get_uint64_t();
      Constant *XorKey = ConstantInt::get(intType, V, false);

      Constant *CE = ConstantExpr::getBitCast(
        Callee, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, CalleeNumbering[Callee], false))));

      XorKey = ConstantExpr::getNeg(XorKey);
      XorKey = ConstantExpr::getXor(XorKey, AddKey);
      XorKey = ConstantExpr::getNeg(XorKey);
      XorKeys.push_back(XorKey);
      Elements.push_back(CE);
    }

    ArrayType *ATy =
      ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));
    GVAdd = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
      CA, GVNameAdd);
    appendToCompilerUsed(*F.getParent(), {GVAdd});

    ArrayType *XTy = ArrayType::get(intType, XorKeys.size());
    Constant *CX = ConstantArray::get(XTy, XorKeys);
    GVXor = new GlobalVariable(*F.getParent(), XTy, false, GlobalValue::LinkageTypes::PrivateLinkage, CX, GVNameXor);
    appendToCompilerUsed(*F.getParent(), {GVXor});

    return std::make_pair(GVAdd, GVXor);
  }

  bool runOnFunction(Function &Fn) override {
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->iCallOpt(), &Fn);
    if (!opt.isEnabled()) {
      return false;
    }

    LLVMContext &Ctx = Fn.getContext();

    CalleeNumbering.clear();
    Callees.clear();
    CallSites.clear();

    NumberCallees(Fn);

    if (Callees.empty()) {
      return false;
    }

    uint64_t V = RandomEngine.get_uint64_t();
    uint64_t XV = RandomEngine.get_uint64_t();

    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }
    ConstantInt *EncKey = ConstantInt::get(intType, V, false);
    ConstantInt *EncKey1 = ConstantInt::get(intType, -V, false);
    ConstantInt *Zero = ConstantInt::get(intType, 0);

    GlobalVariable *GXorKey = nullptr;
    GlobalVariable *Targets = nullptr;
    GlobalVariable *XorKeys = nullptr;

    if (opt.level() == 0) {
      Targets = getIndirectCallees0(Fn, EncKey1);
    } else if (opt.level() == 1 || opt.level() == 2) {
      ConstantInt *CXK = ConstantInt::get(intType, XV, false);
      GXorKey = new GlobalVariable(*Fn.getParent(), CXK->getType(), false, GlobalValue::LinkageTypes::PrivateLinkage,
        CXK, Fn.getName() + "_ICallXorKey");
      appendToCompilerUsed(*Fn.getParent(), {GXorKey});

      if (opt.level() == 1) {
        Targets = getIndirectCallees1(Fn, EncKey1, CXK);
      } else {
        Targets = getIndirectCallees2(Fn, EncKey1, CXK);
      }
    } else {
      auto [fst, snd] = getIndirectCallees3(Fn, EncKey1);
      Targets = fst;
      XorKeys = snd;
    }

    for (auto CI : CallSites) {

      CallBase *CB = CI;

      Function *Callee = CB->getCalledFunction();
      FunctionType *FTy = Callee->getFunctionType();
      IRBuilder<> IRB(CB);

      Value *Idx = ConstantInt::get(intType, CalleeNumbering[CB->getCalledFunction()]);
      Value *GEP = IRB.CreateGEP(
          Targets->getValueType(), Targets,
          {Zero, Idx});
      Value *EncDestAddr = IRB.CreateLoad(
          GEP->getType(), GEP,
          CI->getName());

      Value *DecKey = EncKey;

      if (GXorKey) {
        LoadInst *XorKey = IRB.CreateLoad(GXorKey->getValueType(), GXorKey);

        if (opt.level() == 1) {
          DecKey = IRB.CreateXor(EncKey1, XorKey);
          DecKey = IRB.CreateNeg(DecKey);
        } else if (opt.level() == 2) {
          DecKey = IRB.CreateXor(EncKey1, IRB.CreateMul(XorKey, Idx));
          DecKey = IRB.CreateNeg(DecKey);
        }
      }

      if (XorKeys) {
        Value *XorKeysGEP = IRB.CreateGEP(XorKeys->getValueType(), XorKeys, {Zero, Idx});
        
        Value *XorKey = IRB.CreateLoad(intType, XorKeysGEP);

        XorKey = IRB.CreateNeg(XorKey);
        XorKey = IRB.CreateXor(XorKey, EncKey1);
        XorKey = IRB.CreateNeg(XorKey);

        DecKey = IRB.CreateXor(EncKey1, IRB.CreateMul(XorKey, Idx));
        DecKey = IRB.CreateNeg(DecKey);
      }

      Value *DestAddr = IRB.CreateGEP(Type::getInt8Ty(Ctx),
          EncDestAddr, DecKey);

      Value *FnPtr = IRB.CreateBitCast(DestAddr, FTy->getPointerTo());
      FnPtr->setName("Call_" + Callee->getName());
      CB->setCalledOperand(FnPtr);
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
