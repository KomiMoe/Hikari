#ifndef __UTILS_OBF__
#define __UTILS_OBF__

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/Local.h" // For DemoteRegToStack and DemotePHIToStack

using namespace llvm;

bool valueEscapes(Instruction *Inst);
void fixStack(Function *f);
CallBase* fixEH(CallBase* CB);
void LowerConstantExpr(Function &F);
bool expandConstantExpr(Function &F);

#endif
