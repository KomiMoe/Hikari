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
  std::map<BasicBlock *, unsigned> BBNumbering;
  std::vector<BasicBlock *> BBTargets;        //all conditional branch targets
  CryptoUtils RandomEngine;

  IndirectBranch(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  StringRef getPassName() const override { return {"IndirectBranch"}; }

  void NumberBasicBlock(Function &F) {
    for (auto &BB : F) {
      if (auto *BI = dyn_cast<BranchInst>(BB.getTerminator())) {
        if (BI->isConditional()) {
          unsigned N = BI->getNumSuccessors();
          for (unsigned I = 0; I < N; I++) {
            BasicBlock *Succ = BI->getSuccessor(I);
            if (BBNumbering.count(Succ) == 0) {
              BBTargets.push_back(Succ);
              BBNumbering[Succ] = 0;
            }
          }
        }
      }
    }

    long seed = RandomEngine.get_uint32_t();
    std::default_random_engine e(seed);
    std::shuffle(BBTargets.begin(), BBTargets.end(), e);

    unsigned N = 0;
    for (auto BB:BBTargets) {
      BBNumbering[BB] = N++;
    }
  }

  GlobalVariable *getIndirectTargets0(Function &F, ConstantInt *EncKey) const {
    std::string GVName(F.getName().str() + "_IndirectBrTargets");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    // encrypt branch targets
    std::vector<Constant *> Elements;
    for (const auto BB:BBTargets) {
      Constant *CE = ConstantExpr::getBitCast(BlockAddress::get(BB), PointerType::getUnqual(F.getContext()));
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

  GlobalVariable *getIndirectTargets1(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) const {
    std::string GVName(F.getName().str() + "_IndirectBrTargets1");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    // encrypt branch targets
    std::vector<Constant *> Elements;
    for (const auto BB:BBTargets) {
      Constant *CE = ConstantExpr::getBitCast(BlockAddress::get(BB), PointerType::getUnqual(F.getContext()));
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

  GlobalVariable *getIndirectTargets2(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) {
    std::string GVName(F.getName().str() + "_IndirectBrTargets2");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }
    // encrypt branch targets
    std::vector<Constant *> Elements;
    for (auto BB:BBTargets) {
      Constant *CE = ConstantExpr::getBitCast(BlockAddress::get(BB), PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, BBNumbering[BB], false))));
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

  std::pair<GlobalVariable *, GlobalVariable *> getIndirectTargets3(Function &F, ConstantInt *AddKey) {
    std::string GVNameAdd(F.getName().str() + "_IndirectBrTargets3");
    std::string GVNameXor(F.getName().str() + "_IndirectBr3_Xor");
    GlobalVariable *GVAdd = F.getParent()->getNamedGlobal(GVNameAdd);
    GlobalVariable *GVXor = F.getParent()->getNamedGlobal(GVNameXor);

    if (GVAdd && GVXor)
      return std::make_pair(GVAdd, GVXor);

    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    // encrypt branch targets
    std::vector<Constant *> Elements;
    std::vector<Constant *> XorKeys;
    for (auto BB:BBTargets) {
      uint64_t V = RandomEngine.get_uint64_t();
      Constant *XorKey = ConstantInt::get(intType, V, false);
      Constant *CE = ConstantExpr::getBitCast(BlockAddress::get(BB), PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, BBNumbering[BB], false))));

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

    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->indBrOpt(), &Fn);

    if (!opt.isEnabled()) {
      return false;
    }

    if (Fn.empty() || Fn.hasLinkOnceLinkage() || Fn.getSection() == ".text.startup") {
      return false;
    }

    LLVMContext &Ctx = Fn.getContext();

    // Init member fields
    BBNumbering.clear();
    BBTargets.clear();

    // llvm cannot split critical edge from IndirectBrInst
    SplitAllCriticalEdges(Fn, CriticalEdgeSplittingOptions(nullptr, nullptr));
    NumberBasicBlock(Fn);

    if (BBNumbering.empty()) {
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
    GlobalVariable *DestBBs = nullptr;
    GlobalVariable *XorKeys = nullptr;

    if (opt.level() == 0) {
      DestBBs = getIndirectTargets0(Fn, EncKey1);
    } else if (opt.level() == 1 || opt.level() == 2) {
      ConstantInt *CXK = ConstantInt::get(intType, XV, false);
      GXorKey = new GlobalVariable(*Fn.getParent(), CXK->getType(), false, GlobalValue::LinkageTypes::PrivateLinkage,
        CXK, Fn.getName() + "_IBrXorKey");
      appendToCompilerUsed(*Fn.getParent(), {GXorKey});
      if (opt.level() == 1) {
        DestBBs = getIndirectTargets1(Fn, EncKey1, CXK);
      } else {
        DestBBs = getIndirectTargets2(Fn, EncKey1, CXK);
      }
    } else {
      auto [fst, snd] = getIndirectTargets3(Fn, EncKey1);
      DestBBs = fst;
      XorKeys = snd;
    }

    for (auto &BB : Fn) {
      auto *BI = dyn_cast<BranchInst>(BB.getTerminator());
      if (BI && BI->isConditional()) {
        IRBuilder<> IRB(BI);

        Value *Cond = BI->getCondition();
        Value *Idx;
        Value *TIdx, *FIdx;

        TIdx = ConstantInt::get(intType, BBNumbering[BI->getSuccessor(0)]);
        FIdx = ConstantInt::get(intType, BBNumbering[BI->getSuccessor(1)]);
        Idx = IRB.CreateSelect(Cond, TIdx, FIdx);

        Value *GEP = IRB.CreateGEP(
          DestBBs->getValueType(), DestBBs,
            {Zero, Idx});
        Value *EncDestAddr = IRB.CreateLoad(
            GEP->getType(),
            GEP,
            "EncDestAddr");
        // -EncKey = X - FuncSecret
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

        Value *DestAddr = IRB.CreateGEP(
          Type::getInt8Ty(Ctx),
            EncDestAddr, DecKey);

        IndirectBrInst *IBI = IndirectBrInst::Create(DestAddr, 2);
        IBI->addDestination(BI->getSuccessor(0));
        IBI->addDestination(BI->getSuccessor(1));
        ReplaceInstWithInst(BI, IBI);
      }
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
