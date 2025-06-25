#ifndef OBFUSCATION_OBFUSCATIONOPTIONS_H
#define OBFUSCATION_OBFUSCATIONOPTIONS_H

#include <set>
#include <llvm/Support/YAMLParser.h>
#include <llvm/IR/Function.h>


namespace llvm {

SmallVector<std::string> readAnnotate(Function *f);

class ObfOpt {
protected:
  uint32_t    Enabled : 1;
  uint32_t    Level   : 2;
  std::string AttributeName;

public:
  ObfOpt(bool enable, uint32_t level, const std::string &attributeName) {
    this->Enabled = enable;
    this->Level = std::min<uint32_t>(level, 3);
    this->AttributeName = attributeName;
  }

  void setEnable(bool enabled) {
    this->Enabled = enabled;
  }

  void setLevel(uint32_t level) {
    this->Level = std::min<uint32_t>(level, 3);
  }

  bool isEnabled() const {
    return this->Enabled;
  }

  uint32_t level() const {
    return this->Level;
  }

  const std::string &attributeName() const {
    return this->AttributeName;
  }

  ObfOpt none() const {
    return ObfOpt{false, 0, this->attributeName()};
  }

};

class ObfuscationOptions {
protected:
  ObfOpt *IndBrOpt = nullptr;
  ObfOpt *ICallOpt = nullptr;
  ObfOpt *IndGvOpt = nullptr;
  ObfOpt *FlaOpt = nullptr;
  ObfOpt *CseOpt = nullptr;
  ObfOpt *CieOpt = nullptr;
  ObfOpt *CfeOpt = nullptr;

public:
  ObfuscationOptions(ObfOpt *indBrOpt, ObfOpt *iCallOpt, ObfOpt *indGvOpt,
                     ObfOpt *flaOpt, ObfOpt *  cseOpt, ObfOpt *  cieOpt,
                     ObfOpt *cfeOpt) {
    this->IndBrOpt = indBrOpt;
    this->ICallOpt = iCallOpt;
    this->IndGvOpt = indGvOpt;
    this->FlaOpt = flaOpt;
    this->CseOpt = cseOpt;
    this->CieOpt = cieOpt;
    this->CfeOpt = cfeOpt;
  }

  auto indBrOpt() const {
    return IndBrOpt;
  }

  auto iCallOpt() const {
    return ICallOpt;
  }

  auto indGvOpt() const {
    return IndGvOpt;
  }

  auto flaOpt() const {
    return FlaOpt;
  }

  auto cseOpt() const {
    return CseOpt;
  }

  auto cieOpt() const {
    return CieOpt;
  }

  auto cfeOpt() const {
    return CfeOpt;
  }

  static ObfOpt toObfuscate(const ObfOpt *option, Function *f);

};

}

#endif