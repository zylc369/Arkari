#include "llvm/Support/ErrorOr.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DiagnosticInfo.h"

using namespace llvm;

namespace llvm {

// 读取给定函数 f 的所有注解（annotations）
// 这些注解存储在全局变量 "llvm.global.annotations" 中
// 返回值是一个字符串列表，包含所有与该函数相关的注解
SmallVector<std::string> readAnnotate(Function *f) {
  SmallVector<std::string> annotations;

  // 获取全局注解变量
  auto *Annotations = f->getParent()->getGlobalVariable(
      "llvm.global.annotations");
  auto *C = dyn_cast_or_null<Constant>(Annotations);
  if (!C || C->getNumOperands() != 1)
    return annotations;

  // 获取注解结构体数组
  C = cast<Constant>(C->getOperand(0));

  // 遍历所有注解项
  // Iterate over all entries in C and attach !annotation metadata to suitable
  // entries.
  for (auto &Op : C->operands()) {
    // Look at the operands to check if we can use the entry to generate
    // !annotation metadata.
    auto *OpC = dyn_cast<ConstantStruct>(&Op);
    if (!OpC || OpC->getNumOperands() < 2)
      continue;
    // 第一个字段是函数指针，检查是否是我们需要的函数
    auto *Fn = dyn_cast<Function>(OpC->getOperand(0)->stripPointerCasts());
    if (Fn != f)
      continue;
    // 第二个字段是字符串常量，指向注解内容
    auto *StrC = dyn_cast<GlobalValue>(OpC->getOperand(1)->stripPointerCasts());
    if (!StrC)
      continue;
    // 获取字符串数据
    auto *StrData = dyn_cast<ConstantDataSequential>(StrC->getOperand(0));
    if (!StrData)
      continue;
    // 添加到结果中
    annotations.emplace_back(StrData->getAsString());
  }

  return annotations;
}

// 判断是否对函数 f 应用某种混淆选项 ObfOpt
ObfOpt ObfuscationOptions::toObfuscate(const ObfOpt *option, Function *f) {
  // 启用混淆的注解前缀
  const auto attrEnable = "+" + option->attributeName();
  // 禁用混淆的注解前缀
  const auto attrDisable = "-" + option->attributeName();
  // 设置混淆强度的前缀
  const auto attrLevel = "^" + option->attributeName();
  // 初始化为默认配置（不启用）
  ObfOpt     result = option->none();
  // 如果是声明或外部链接的函数，不进行混淆
  if (f->isDeclaration()) {
    return result;
  }

  if (f->hasAvailableExternallyLinkage() != 0) {
    return result;
  }

  // 是否找到启用注解
  bool annotationEnableFound = false;
  // 是否找到禁用注解
  bool annotationDisableFound = false;

  // 获取函数的所有注解
  auto annotations = readAnnotate(f);
  // 记录设置的强度等级数量
  int  levelSet = 0;
  // 遍历所有注解
  if (!annotations.empty()) {
    for (const auto &annotation : annotations) {
      // 检查是否是禁用注解
      if (annotation.find(attrDisable) != std::string::npos) {
        result.setEnable(false);
        annotationDisableFound = true;
      }
      // 检查是否是启用注解
      if (annotation.find(attrEnable) != std::string::npos) {
        result.setEnable(true);
        annotationEnableFound = true;
      }
      // 检查是否是设置强度等级的注解
      if (const auto levelPos = annotation.find(attrLevel);
        levelPos != std::string::npos) {
        // 检查是否重复设置了多个等级
        if (annotation.find(attrLevel, levelPos + 1) != std::string::npos) {
          f->getContext().diagnose(DiagnosticInfoUnsupported{
              *f,
              f->getName() + " has multiple annotations for setting " + result.
              attributeName() +
              " factors, What are you the fucking want to do?"});
          return result.none();
        }
        int32_t    level = -1;
        const auto equalPos = annotation.find('=', levelPos + 1);
        if (equalPos == std::string::npos) {
          f->getContext().diagnose(DiagnosticInfoUnsupported{
              *f,
              f->getName() + ": " + annotation +
              " missing equal sign, sample: " + attrLevel + " = 0"});
          return result.none();
        }

        // 检查等号前是否有非法字符
        for (size_t i = levelPos + attrLevel.length(); i < equalPos; ++i) {
          if (annotation[i] == ' ') {
            continue;
          }
          f->getContext().diagnose(DiagnosticInfoUnsupported{
              *f,
              f->getName() + ": " + annotation +
              " unexpected characters, sample: " + attrLevel + " = 0"});
          return result.none();
        }

        // 解析等号后的数字
        for (size_t i = equalPos + 1; i < annotation.length(); ++i) {
          if (annotation[i] == ' ') {
            continue;
          }
          level = annotation[i] - '0';
          if (level < 0 || level > 9) {
            f->getContext().diagnose(DiagnosticInfoUnsupported{
              *f,
              f->getName() + ": " + annotation +
              " unexpected character: " + std::string{annotation[i]} + ", sample: " + attrLevel + " = 0"});
            return result.none();
          }
          break;
        }
        if (level == -1) {
          f->getContext().diagnose(DiagnosticInfoUnsupported{
              *f,
              f->getName() + ": " + annotation +
              " level value not found, sample: " + attrLevel + " = 0"});
          return result.none();
        }

        ++levelSet;
        result.setLevel(level);
      }
    }
  }

  // 如果同时存在启用和禁用注解，报错并返回 none
  if (annotationDisableFound && annotationEnableFound) {
    f->getContext().diagnose(DiagnosticInfoUnsupported{
        *f,
        f->getName() +
        " having both enable annotation and disable annotation, What are you the fucking want to do?"});
    return result.none();
  }

  // 如果设置了多个强度等级，报错并返回 none
  if (levelSet > 1) {
    f->getContext().diagnose(DiagnosticInfoUnsupported{
        *f,
        f->getName() + " has multiple annotations for setting " + result.
        attributeName() + " factors, What are you the fucking want to do?"});
    return result.none();
  }

  // 如果没有找到显式的启用/禁用标志，则使用全局配置
  if (!annotationDisableFound && !annotationEnableFound) {
    result.setEnable(option->isEnabled());
  }
  // 如果没有设置强度等级，则使用全局配置
  if (!levelSet) {
    result.setLevel(option->level());
  }
  return result;
}


}
