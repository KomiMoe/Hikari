#ifndef __UTILS_OBF__
#define __UTILS_OBF__

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/Local.h" // For DemoteRegToStack and DemotePHIToStack

#include <unordered_map>
#include <set>
#include <vector>

namespace llvm {
  class CryptoUtils;
}

using namespace llvm;
struct CreatePageTableArgs {
  unsigned CountLoop;
  std::string GVNamePrefix;
  CryptoUtils* RandomEngine;
  Module* M;
  std::vector<Constant *> *Objects;
  std::unordered_map<Constant *, unsigned> *IndexMap;
  std::unordered_map<Constant *, uint64_t> *ObjectKeys;
  std::vector<GlobalVariable *> *OutPageTable;
};


struct BuildDecryptArgs {
  unsigned FuncLoopCount;
  unsigned NextIndex;
  Value *NextIndexValue;
  Function *Fn;
  Instruction *InsertBefore;
  Type *LoadTy;
  std::vector<GlobalVariable *> *ModulePageTable;
  std::vector<GlobalVariable *> *FuncPageTable;
  uint64_t ModuleKey;
  uint64_t FuncKey;
};

bool valueEscapes(Instruction *Inst);
void fixStack(Function *f);
CallBase* fixEH(CallBase* CB);
void LowerConstantExpr(Function &F);
bool expandConstantExpr(Function &F);
void createPageTable(const CreatePageTableArgs& args);
void enhancedPageTable(const CreatePageTableArgs& args, std::unordered_map<Constant *, unsigned> *FuncIndexMap);
Value * buildPageTableDecryptIR(const BuildDecryptArgs& args);
Value * encryptConstant(Constant *plainConstant, Instruction *insertBefore, CryptoUtils *randomEngine, unsigned level);
#endif
