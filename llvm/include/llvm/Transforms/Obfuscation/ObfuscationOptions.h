#ifndef OBFUSCATION_OBFUSCATIONOPTIONS_H
#define OBFUSCATION_OBFUSCATIONOPTIONS_H

#include "llvm/Support/YAMLParser.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"


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

  ObfOpt(const std::string &attributeName) {
    this->Enabled = false;
    this->Level = 0;
    this->AttributeName = attributeName;
  }

  void readOpt(const cl::opt<bool>& enableOpt) {
    if (enableOpt.getNumOccurrences()) {
      Enabled = enableOpt.getValue();
    }
  }

  void readOpt(const cl::opt<bool>& enableOpt, const cl::opt<uint32_t>& levelOpt) {
    readOpt(enableOpt);
    if (levelOpt.getNumOccurrences()) {
      Level = levelOpt.getValue();
    }
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
  std::shared_ptr<ObfOpt> IndBrOpt = nullptr;
  std::shared_ptr<ObfOpt> ICallOpt = nullptr;
  std::shared_ptr<ObfOpt> IndGvOpt = nullptr;
  std::shared_ptr<ObfOpt> FlaOpt = nullptr;
  std::shared_ptr<ObfOpt> CseOpt = nullptr;
  std::shared_ptr<ObfOpt> CieOpt = nullptr;
  std::shared_ptr<ObfOpt> CfeOpt = nullptr;

public:
  SmallVector<std::shared_ptr<ObfOpt>> getAllOpt() const {
    SmallVector<std::shared_ptr<ObfOpt>, 7> allOpt;
    allOpt.push_back(IndBrOpt);
    allOpt.push_back(ICallOpt);
    allOpt.push_back(IndGvOpt);
    allOpt.push_back(FlaOpt);
    allOpt.push_back(CseOpt);
    allOpt.push_back(CieOpt);
    allOpt.push_back(CfeOpt);
    return allOpt;
  }

  ObfuscationOptions(const std::shared_ptr<ObfOpt> &indBrOpt,
                     const std::shared_ptr<ObfOpt> &iCallOpt,
                     const std::shared_ptr<ObfOpt> &indGvOpt,
                     const std::shared_ptr<ObfOpt> &flaOpt,
                     const std::shared_ptr<ObfOpt> &cseOpt,
                     const std::shared_ptr<ObfOpt> &cieOpt,
                     const std::shared_ptr<ObfOpt> &cfeOpt) {
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

  static std::shared_ptr<ObfuscationOptions> readConfigFile(
      const Twine& FileName);

  static ObfOpt toObfuscate(const std::shared_ptr<ObfOpt>& option, Function* f);

};

}

#endif