#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/EHPersonalities.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/CryptoUtils.h"

#include <random>

// Shamefully borrowed from ../Scalar/RegToMem.cpp :(
bool valueEscapes(Instruction *Inst) {
  BasicBlock *BB = Inst->getParent();
  for (Value::use_iterator UI = Inst->use_begin(), E = Inst->use_end(); UI != E;
       ++UI) {
    Instruction *I = cast<Instruction>(*UI);
    if (I->getParent() != BB || isa<PHINode>(I)) {
      return true;
    }
  }
  return false;
}

void fixStack(Function *f) {
  // Try to remove phi node and demote reg to stack
  std::vector<PHINode *>     tmpPhi;
  std::vector<Instruction *> tmpReg;
  BasicBlock *               bbEntry = &*f->begin();

  do {
    tmpPhi.clear();
    tmpReg.clear();

    for (Function::iterator i = f->begin(); i != f->end(); ++i) {

      for (BasicBlock::iterator j = i->begin(); j != i->end(); ++j) {

        if (isa<PHINode>(j)) {
          PHINode *phi = cast<PHINode>(j);
          tmpPhi.push_back(phi);
          continue;
        }
        if (!(isa<AllocaInst>(j) && j->getParent() == bbEntry) &&
            (valueEscapes(&*j) || j->isUsedOutsideOfBlock(&*i))) {
          tmpReg.push_back(&*j);
          continue;
        }
      }
    }
    for (unsigned int i = 0; i != tmpReg.size(); ++i) {
      DemoteRegToStack(*tmpReg.at(i));
    }

    for (unsigned int i = 0; i != tmpPhi.size(); ++i) {
      DemotePHIToStack(tmpPhi.at(i));
    }

  } while (tmpReg.size() != 0 || tmpPhi.size() != 0);
}

CallBase* fixEH(CallBase* CB) {
  const auto BB = CB->getParent();
  if (!BB) {
    return CB;
  }
  const auto Fn = BB->getParent();
  if (!Fn || !Fn->hasPersonalityFn()
    || !isScopedEHPersonality(classifyEHPersonality(Fn->getPersonalityFn()))) {
    return CB;
  }
  const auto BlockColors = colorEHFunclets(*Fn);
  const auto BBColor = BlockColors.find(BB);
  if (BBColor == BlockColors.end()) {
    return CB;
  }
  const auto& ColorVec = BBColor->getSecond();
  assert(ColorVec.size() == 1 && "non-unique color for block!");

  const auto EHBlock = ColorVec.front();
  if (!EHBlock || !EHBlock->isEHPad()) {
    return CB;
  }
  const auto EHPad = EHBlock->getFirstNonPHI();

  const OperandBundleDef OB("funclet", EHPad);
  auto *NewCall = CallBase::addOperandBundle(CB, LLVMContext::OB_funclet, OB, CB);
  NewCall->copyMetadata(*CB);
  CB->replaceAllUsesWith(NewCall);
  CB->eraseFromParent();
  return NewCall;
}

void LowerConstantExpr(Function &F) {
  SmallPtrSet<Instruction *, 8> WorkList;

  for (inst_iterator It = inst_begin(F), E = inst_end(F); It != E; ++It) {
    Instruction *I = &*It;

    if (isa<LandingPadInst>(I) || isa<CatchPadInst>(I) || isa<
          CatchSwitchInst>(I) || isa<CatchReturnInst>(I))
      continue;
    if (auto *II = dyn_cast<IntrinsicInst>(I)) {
      if (II->getIntrinsicID() == Intrinsic::eh_typeid_for) {
        continue;
      }
    }

    for (unsigned int i = 0; i < I->getNumOperands(); ++i) {
      if (isa<ConstantExpr>(I->getOperand(i)))
        WorkList.insert(I);
    }
  }

  while (!WorkList.empty()) {
    auto         It = WorkList.begin();
    Instruction *I = *It;
    WorkList.erase(*It);

    if (PHINode *PHI = dyn_cast<PHINode>(I)) {
      for (unsigned int i = 0; i < PHI->getNumIncomingValues(); ++i) {
        Instruction *TI = PHI->getIncomingBlock(i)->getTerminator();
        if (ConstantExpr *CE = dyn_cast<
          ConstantExpr>(PHI->getIncomingValue(i))) {
          Instruction *NewInst = CE->getAsInstruction();
          NewInst->insertBefore(TI);
          PHI->setIncomingValue(i, NewInst);
          WorkList.insert(NewInst);
        }
      }
    } else {
      for (unsigned int i = 0; i < I->getNumOperands(); ++i) {
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(I->getOperand(i))) {
          Instruction *NewInst = CE->getAsInstruction();
          NewInst->insertBefore(I);
          I->replaceUsesOfWith(CE, NewInst);
          WorkList.insert(NewInst);
        }
      }
    }
  }
}

bool expandConstantExpr(Function &F) {
  bool                Changed = false;
  LLVMContext &       Ctx = F.getContext();
  IRBuilder<NoFolder> IRB(Ctx);

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
        if (auto CEP = dyn_cast<ConstantExpr>(Opr)) {
          IRB.SetInsertPoint(InsertPt);
          auto CEPInst = CEP->getAsInstruction();
          IRB.Insert(CEPInst);
          I.setOperand(i, CEPInst);
          Changed = true;
        }
      }
    }
  }
  return Changed;
}

void maskCipher(uint8_t mask, uint8_t &lastIndex, APInt &preIndex, unsigned objKey, unsigned newIndex) {
  switch (mask) {
  case 1:
    if (lastIndex != 1) {
      preIndex = -preIndex;
      lastIndex = 1;
      break;
    }
  case 2:
    if (lastIndex != 2) {
      preIndex = preIndex.rotl(objKey + newIndex);
      lastIndex = 2;
      break;
    }
  case 3:
    if (lastIndex != 3) {
      preIndex = preIndex.byteSwap();
      lastIndex = 3;
      break;
    }
  case 4:
    if (lastIndex != 4) {
      preIndex = ~preIndex;
      lastIndex = 4;
      break;
    }
  case 5:
    if (lastIndex != 5) {
      preIndex = preIndex.rotr(objKey - newIndex);
      lastIndex = 5;
      break;
    }
  default:
    if (lastIndex == 0) {
      preIndex = -preIndex;
      lastIndex = 1;
      break;
    }
    preIndex = preIndex ^ objKey;
    lastIndex = 0;
    break;
  }
}

void createPageTable(const CreatePageTableArgs &args) {
  const auto Int32Ty = IntegerType::getInt32Ty(args.M->getContext());
  std::mt19937_64 re(args.RandomEngine->get_uint64_t());
  std::shuffle(args.Objects->begin(), args.Objects->end(), re);

  std::vector<Constant *> GVObjects;
  for (unsigned i = 0; i < args.Objects->size(); ++i) {
    auto Obj = args.Objects->at(i);
    GVObjects.push_back(ConstantExpr::getBitCast(Obj, PointerType::getUnqual(Obj->getType())));
    args.IndexMap->insert_or_assign(Obj, i);
  }

  {
    auto GVNameObjects(args.GVNamePrefix + "_objects");
    auto ATy = ArrayType::get(GVObjects[0]->getType(), GVObjects.size());
    auto CA = ConstantArray::get(ATy, ArrayRef(GVObjects));
    auto GV = new GlobalVariable(*args.M, ATy, false, 
                                 GlobalValue::LinkageTypes::InternalLinkage,
                                 CA, GVNameObjects);
    GV->addMetadata("noobf", *MDNode::get(args.M->getContext(), {}));
    args.OutPageTable->push_back(GV);
  }

  for (unsigned i = 0; i < args.CountLoop; ++i) {
    std::shuffle(args.Objects->begin(), args.Objects->end(), re);

    std::vector<Constant *> ConstantObjectIndex;
    for (unsigned j = 0; j < args.Objects->size(); ++j) {
      const auto Obj = args.Objects->at(j);
      const auto ObjFullKey = args.ObjectKeys->at(Obj);
      const auto ObjKey = static_cast<uint32_t>(ObjFullKey);
      const auto ObjMask = static_cast<uint32_t>(ObjFullKey >> 32);

      APInt preIndex(32, args.IndexMap->at(Obj));
      uint8_t lastIndex = 0xff;
      for (unsigned k = 0; k < 8; ++k) {
        const auto mask = static_cast<uint8_t>(ObjMask >> (k * 3)) % 6u;
        maskCipher(mask, lastIndex, preIndex, ObjKey, j);
      }
      auto toWriteData = ConstantInt::get(Int32Ty, preIndex);
      ConstantObjectIndex.push_back(toWriteData);
      args.IndexMap->insert_or_assign(Obj, j);
    }

    {

      auto GVNameObjPageTable(args.GVNamePrefix + "_page_table_" + std::to_string(i));
      auto IATy = ArrayType::get(Int32Ty, ConstantObjectIndex.size());
      auto IA = ConstantArray::get(IATy, ArrayRef(ConstantObjectIndex));
      auto GV = new GlobalVariable(*args.M, IATy, false,
                                   GlobalValue::LinkageTypes::InternalLinkage,
                                   IA, GVNameObjPageTable);
      GV->addMetadata("noobf", *MDNode::get(args.M->getContext(), {}));
      args.OutPageTable->push_back(GV);
    }
  }

}

void enhancedPageTable(const CreatePageTableArgs &args, std::unordered_map<Constant *, unsigned> *FuncIndexMap) {
  const auto Int32Ty = IntegerType::getInt32Ty(args.M->getContext());
  std::mt19937_64 re(args.RandomEngine->get_uint64_t());

  for (unsigned i = 0; i < args.CountLoop; ++i) {
    std::shuffle(args.Objects->begin(), args.Objects->end(), re);
    std::vector<Constant *> ConstantObjectIndex;
    for (unsigned j = 0; j < args.Objects->size(); ++j) {
      auto Obj = args.Objects->at(j);
      const auto ObjFullKey = args.ObjectKeys->at(Obj);
      const auto ObjKey = static_cast<uint32_t>(ObjFullKey);
      const auto ObjMask = static_cast<uint32_t>(ObjFullKey >> 32);

      APInt preIndex(32, FuncIndexMap->find(Obj) == FuncIndexMap->end() ?
                           args.IndexMap->at(Obj) :
                           FuncIndexMap->at(Obj));

      uint8_t lastIndex = 0xff;
      for (unsigned k = 0; k < 4 * args.CountLoop; ++k) {
        const auto mask = static_cast<uint8_t>(ObjMask >> (k * 2)) % 6u;
        maskCipher(mask, lastIndex, preIndex, ObjKey, j);
      }
      auto toWriteData = ConstantInt::get(Int32Ty, preIndex);
      ConstantObjectIndex.push_back(toWriteData);
      FuncIndexMap->insert_or_assign(Obj, j);
    }

    {
      auto GVNameObjPage(args.GVNamePrefix + "_enhanced_page_table_" + std::to_string(i));
      auto IATy = ArrayType::get(Int32Ty, ConstantObjectIndex.size());
      auto IA = ConstantArray::get(IATy, ArrayRef(ConstantObjectIndex));
      auto GV = new GlobalVariable(*args.M, IATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
        IA, GVNameObjPage);
      GV->addMetadata("noobf", *MDNode::get(args.M->getContext(), {}));
      args.OutPageTable->push_back(GV);
    }
  }
}

Value * buildPageTableDecryptIR(const BuildDecryptArgs &args) {
  auto M = args.Fn->getParent();
  auto& Ctx = args.Fn->getContext();
  auto Int32Ty = IntegerType::getInt32Ty(Ctx);
  auto Zero = ConstantInt::getNullValue(Int32Ty);
  const auto ModuleKey = static_cast<uint32_t>(args.ModuleKey);
  const auto ModuleMask = static_cast<uint32_t>(args.ModuleKey >> 32);
  const auto FuncKey = static_cast<uint32_t>(args.FuncKey);
  const auto FuncMask = static_cast<uint32_t>(args.FuncKey >> 32);
  IRBuilder<> IRB{args.InsertBefore};

  Value *NextIndex = args.NextIndexValue;
  if (!NextIndex) {
    auto GVInitIndex = new GlobalVariable(*M, Int32Ty, false, GlobalValue::PrivateLinkage,
      ConstantInt::get(Int32Ty, args.NextIndex), 
      M->getName() + args.Fn->getName() + "_InitIndex" +
      std::to_string(args.NextIndex));
    GVInitIndex->addMetadata("noobf", *MDNode::get(Ctx, {}));
    NextIndex = IRB.CreateAlignedLoad(Int32Ty, GVInitIndex, Align{1}, true);
  }

  auto createDecIndexSwitch = [&IRB, &M](uint8_t mask, Value *NextIndex, Value *PrevIndex, Value* ObjKey) -> Value* {
    switch (mask) {
    case 1:
      // preIndex = -preIndex;
      NextIndex = IRB.CreateNeg(NextIndex);
      break;
    case 2:
      // preIndex = preIndex.rotl(ObjKey + j);
      NextIndex = IRB.CreateCall(
        Intrinsic::getOrInsertDeclaration(M, Intrinsic::fshr, {NextIndex->getType()}),
        {NextIndex, NextIndex, IRB.CreateAdd(ObjKey, PrevIndex)});
      break;
    case 3:
      // preIndex = preIndex.byteSwap();
      NextIndex = IRB.CreateCall(
        Intrinsic::getOrInsertDeclaration(M, Intrinsic::bswap, {NextIndex->getType()}),
        {NextIndex});
      break;
    case 4:
      // preIndex.flipAllBits();
      NextIndex = IRB.CreateNot(NextIndex);
      break;
    case 5:
      // preIndex = preIndex.rotr(ObjKey - j);
      NextIndex = IRB.CreateCall(
        Intrinsic::getOrInsertDeclaration(M, Intrinsic::fshl, {NextIndex->getType()}),
        {NextIndex, NextIndex, IRB.CreateSub(ObjKey, PrevIndex)});
      break;
    default:
      // preIndex = preIndex ^ ObjKey;
      NextIndex = IRB.CreateXor(NextIndex, ObjKey);
      break;
    }
    return NextIndex;
  };

  if (args.FuncLoopCount && !args.FuncPageTable->empty()) {
    auto ConstantFuncKey = ConstantInt::get(Int32Ty, FuncKey);

    for (int i = args.FuncPageTable->size() - 1; i >= 0; --i) {
      auto TargetPage = args.FuncPageTable->at(i);
      auto PrevIndex = NextIndex;
      Value *GEP = IRB.CreateGEP(
          TargetPage->getValueType(), TargetPage,
          {Zero, NextIndex});
      NextIndex = IRB.CreateLoad(Int32Ty, GEP);
      std::vector<uint8_t> maskIndex;
      uint8_t lastIndex = 0xff;
      for (unsigned j = 0; j < 4 * args.FuncLoopCount; ++j) {
        auto mask = static_cast<uint8_t>(FuncMask >> (j * 2)) % 6u;
        if (mask == lastIndex) {
          if (mask < 5) {
            mask++;
          } else {
            mask = 0;
          }
        }
        lastIndex = mask;
        maskIndex.push_back(mask);
      }
      for (int j = maskIndex.size() - 1; j >= 0; --j) {
        NextIndex = createDecIndexSwitch(maskIndex.at(j), NextIndex, PrevIndex, ConstantFuncKey);
      }
    }
  }

  auto ConstantModuleKey = ConstantInt::get(Int32Ty, ModuleKey);

  for (int i = args.ModulePageTable->size() - 1; i >= 0; --i) {
    auto TargetPage = args.ModulePageTable->at(i);
    auto PrevIndex = NextIndex;
    Value *GEP = IRB.CreateGEP(
      TargetPage->getValueType(), TargetPage,
      {Zero, NextIndex});
    if (i) {
      NextIndex = IRB.CreateLoad(Int32Ty, GEP);
      std::vector<uint8_t> maskIndex;
      uint8_t lastIndex = 0xff;
      for (unsigned j = 0; j < 8; ++j) {
        auto mask = static_cast<uint8_t>(ModuleMask >> (j * 3)) % 6u;
        if (mask == lastIndex) {
          if (mask < 5) {
            mask++;
          } else {
            mask = 0;
          }
        }
        lastIndex = mask;
        maskIndex.push_back(mask);
      }
      for (int j = maskIndex.size() - 1; j >= 0; --j) {
        NextIndex = createDecIndexSwitch(maskIndex.at(j), NextIndex, PrevIndex, ConstantModuleKey);
      }
      continue;
    }
    return IRB.CreateLoad(args.LoadTy, GEP);
  }
  llvm_unreachable("BuildDecryptIR unreachable!!!");
}

Value * encryptConstant(Constant *plainConstant, Instruction *insertBefore, CryptoUtils *randomEngine, unsigned level) {
  auto& Ctx = insertBefore->getContext();
  auto OriginValTy = plainConstant->getType();
  if (OriginValTy->isStructTy() || OriginValTy->isArrayTy() || OriginValTy->isPointerTy()) {
    return plainConstant;
  }
  auto BitWidth = plainConstant->getType()->getPrimitiveSizeInBits().getFixedValue();
  if (BitWidth < 8) {
    return plainConstant;
  }
  
  const auto Key = ConstantInt::get(
      IntegerType::get(Ctx, BitWidth),
      randomEngine->get_uint64_t());

  const auto ConstantInt = ConstantExpr::getBitCast(plainConstant, Key->getType());
  auto Enc = ConstantExpr::getSub(ConstantInt, Key);
  Constant *XorKey = nullptr;
  if (level) {
    XorKey = ConstantInt::get(Key->getType(), randomEngine->get_uint64_t());
    Enc = ConstantExpr::getXor(Enc, XorKey);
    if (level > 1) {
      Enc = ConstantExpr::getXor(Enc, ConstantExpr::get(Instruction::Mul, XorKey, Key));
    }
    if (level > 2) {
      Enc = ConstantExpr::getXor(Enc, ConstantExpr::getNeg(XorKey));
    }
  }
  auto EncGV = new GlobalVariable(*insertBefore->getModule(), Enc->getType(), false,
                                  GlobalValue::InternalLinkage, Enc);
  EncGV->addMetadata("noobf", *MDNode::get(Ctx, {}));
  IRBuilder<NoFolder> IRB(insertBefore);
  Value *Load = IRB.CreateAlignedLoad(Enc->getType(), EncGV, Align{1}, true);
  if (level) {
    if (level > 2) {
      Load = IRB.CreateXor(Load, IRB.CreateNeg(XorKey));
    }
    if (level > 1) {
      Load = IRB.CreateXor(Load, IRB.CreateMul(XorKey, Key));
    }
    Load = IRB.CreateXor(Load, XorKey);
  }
  Load = IRB.CreateAdd(Load, Key);
  return IRB.CreateBitCast(Load, OriginValTy);
}
