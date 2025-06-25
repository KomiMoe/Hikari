#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Obfuscation/IndirectGlobalVariable.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/Module.h"

#include <random>

#define DEBUG_TYPE "indgv"

using namespace llvm;
namespace {
struct IndirectGlobalVariable : public FunctionPass {
  unsigned pointerSize;
  static char ID;
  
  ObfuscationOptions *ArgsOptions;
  std::map<GlobalVariable *, unsigned> GVNumbering;
  std::vector<GlobalVariable *> GlobalVariables;
  CryptoUtils RandomEngine;

  IndirectGlobalVariable(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  StringRef getPassName() const override { return {"IndirectGlobalVariable"}; }

  void NumberGlobalVariable(Function &F) {
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      for (User::op_iterator op = (*I).op_begin(); op != (*I).op_end(); ++op) {
        Value *val = *op;
        if (GlobalVariable *GV = dyn_cast<GlobalVariable>(val)) {
          if (!GV->isThreadLocal() && GVNumbering.count(GV) == 0 &&
              !GV->isDLLImportDependent()) {
            GVNumbering[GV] = 0;
            GlobalVariables.push_back((GlobalVariable *) val);
          }
        }
      }
    }

    long seed = RandomEngine.get_uint32_t();
    std::default_random_engine e(seed);
    std::shuffle(GlobalVariables.begin(), GlobalVariables.end(), e);
    unsigned N = 0;
    for (auto GV:GlobalVariables) {
      GVNumbering[GV] = N++;
    }
  }

  GlobalVariable *getIndirectGlobalVariables0(Function &F, ConstantInt *EncKey) const {
    std::string GVName(F.getName().str() + "_IndirectGVars");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    std::vector<Constant *> Elements;
    for (auto GVar:GlobalVariables) {
      Constant *CE = ConstantExpr::getBitCast(
          GVar, PointerType::getUnqual(F.getContext()));
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

  GlobalVariable *getIndirectGlobalVariables1(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) const {
    std::string GVName(F.getName().str() + "_IndirectGVars1");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    std::vector<Constant *> Elements;
    for (auto GVar:GlobalVariables) {
      Constant *CE = ConstantExpr::getBitCast(
        GVar, PointerType::getUnqual(F.getContext()));
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

  GlobalVariable *getIndirectGlobalVariables2(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) {
    std::string GVName(F.getName().str() + "_IndirectGVars2");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    std::vector<Constant *> Elements;
    for (auto GVar:GlobalVariables) {
      Constant *CE = ConstantExpr::getBitCast(
        GVar, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, GVNumbering[GVar], false))));
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

  std::pair<GlobalVariable *, GlobalVariable *> getIndirectGlobalVariables3(Function &F, ConstantInt *AddKey) {
    std::string GVNameAdd(F.getName().str() + "_IndirectGVars3");
    std::string GVNameXor(F.getName().str() + "_IndirectGVars3Xor");
    GlobalVariable *GVAdd = F.getParent()->getNamedGlobal(GVNameAdd);
    GlobalVariable *GVXor = F.getParent()->getNamedGlobal(GVNameXor);
    if (GVAdd && GVXor)
      return std::make_pair(GVAdd, GVXor);

    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    std::vector<Constant *> Elements;
    std::vector<Constant *> XorKeys;
    for (auto GVar:GlobalVariables) {
      uint64_t V = RandomEngine.get_uint64_t();
      Constant *XorKey = ConstantInt::get(intType, V, false);

      Constant *CE = ConstantExpr::getBitCast(
        GVar, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, GVNumbering[GVar], false))));
      Elements.push_back(CE);

      XorKey = ConstantExpr::getNeg(XorKey);
      XorKey = ConstantExpr::getXor(XorKey, AddKey);
      XorKey = ConstantExpr::getNeg(XorKey);
      XorKeys.push_back(XorKey);
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
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->indGvOpt(), &Fn);
    if (!opt.isEnabled()) {
      return false;
    }

    LLVMContext &Ctx = Fn.getContext();

    GVNumbering.clear();
    GlobalVariables.clear();

    LowerConstantExpr(Fn);
    NumberGlobalVariable(Fn);

    if (GlobalVariables.empty()) {
      return false;
    }

    uint64_t V = RandomEngine.get_uint64_t();
    uint64_t XV = RandomEngine.get_uint64_t();
    IntegerType* intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    ConstantInt *EncKey = ConstantInt::get(intType, V, false);
    ConstantInt *EncKey1 = ConstantInt::get(intType, -V, false);
    ConstantInt *Zero = ConstantInt::get(intType, 0);

    GlobalVariable *GXorKey = nullptr;
    GlobalVariable *GVars = nullptr;
    GlobalVariable *XorKeys = nullptr;

    if (opt.level() == 0) {
      GVars = getIndirectGlobalVariables0(Fn, EncKey1);
    } else if (opt.level() == 1 || opt.level() == 2) {
      ConstantInt *CXK = ConstantInt::get(intType, XV, false);
      GXorKey = new GlobalVariable(*Fn.getParent(), CXK->getType(), false, GlobalValue::LinkageTypes::PrivateLinkage,
        CXK, Fn.getName() + "_IGVXorKey");
      appendToCompilerUsed(*Fn.getParent(), {GXorKey});
      if (opt.level() == 1) {
        GVars = getIndirectGlobalVariables1(Fn, EncKey1, CXK);
      } else {
        GVars = getIndirectGlobalVariables2(Fn, EncKey1, CXK);
      }
    } else {
      auto [fst, snd] = getIndirectGlobalVariables3(Fn, EncKey1);
      GVars = fst;
      XorKeys = snd;
    }

    for (inst_iterator I = inst_begin(Fn), E = inst_end(Fn); I != E; ++I) {
      Instruction *Inst = &*I;
      if (isa<LandingPadInst>(Inst) || isa<CleanupPadInst>(Inst) ||
          isa<CatchPadInst>(Inst) || isa<CatchReturnInst>(Inst) ||
          isa<CatchSwitchInst>(Inst) || isa<ResumeInst>(Inst) || 
          isa<CallInst>(Inst)) {
        continue;
      }
      if (PHINode *PHI = dyn_cast<PHINode>(Inst)) {
        for (unsigned int i = 0; i < PHI->getNumIncomingValues(); ++i) {
          Value *val = PHI->getIncomingValue(i);
          if (GlobalVariable *GV = dyn_cast<GlobalVariable>(val)) {
            if (GVNumbering.count(GV) == 0) {
              continue;
            }

            Instruction *IP = PHI->getIncomingBlock(i)->getTerminator();
            IRBuilder<> IRB(IP);

            Value *Idx = ConstantInt::get(intType, GVNumbering[GV]);
            Value *GEP = IRB.CreateGEP(
                GVars->getValueType(),
                GVars,
                {Zero, Idx});
            LoadInst *EncGVAddr = IRB.CreateLoad(
                GEP->getType(), GEP,
                GV->getName());

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

            Value *GVAddr = IRB.CreateGEP(
              Type::getInt8Ty(Ctx),
                EncGVAddr,
              DecKey);
            GVAddr = IRB.CreateBitCast(GVAddr, GV->getType());
            GVAddr->setName("IndGV0_");
            PHI->setIncomingValue(i, GVAddr);
          }
        }
      } else {
        for (User::op_iterator op = Inst->op_begin(); op != Inst->op_end(); ++op) {
          if (GlobalVariable *GV = dyn_cast<GlobalVariable>(*op)) {
            if (GVNumbering.count(GV) == 0) {
              continue;
            }

            IRBuilder<> IRB(Inst);
            Value *Idx = ConstantInt::get(intType, GVNumbering[GV]);
            Value *GEP = IRB.CreateGEP(
                GVars->getValueType(),
                GVars,
                {Zero, Idx});
            LoadInst *EncGVAddr = IRB.CreateLoad(
                GEP->getType(),
                GEP,
                GV->getName());

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

            Value *GVAddr = IRB.CreateGEP(
              Type::getInt8Ty(Ctx),
                EncGVAddr,
                DecKey);
            GVAddr = IRB.CreateBitCast(GVAddr, GV->getType());
            GVAddr->setName("IndGV1_");
            Inst->replaceUsesOfWith(GV, GVAddr);
          }
        }
      }
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
