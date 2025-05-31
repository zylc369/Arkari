//===- EHPersonalities.cpp - Compute EH-related information ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/EHPersonalities.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Triple.h"
using namespace llvm;

/// 检查给定的异常处理个性函数是否受支持。若支持则返回其类型描述，否则返回Unknown。
///
/// See if the given exception handling personality function is one that we
/// understand.  If so, return a description of it; otherwise return Unknown.
EHPersonality llvm::classifyEHPersonality(const Value *Pers) {
  const GlobalValue *F =
      Pers ? dyn_cast<GlobalValue>(Pers->stripPointerCasts()) : nullptr;
  if (!F || !F->getValueType() || !F->getValueType()->isFunctionTy())
    return EHPersonality::Unknown;
  return StringSwitch<EHPersonality>(F->getName())
      .Case("__gnat_eh_personality", EHPersonality::GNU_Ada)
      .Case("__gxx_personality_v0", EHPersonality::GNU_CXX)
      .Case("__gxx_personality_seh0", EHPersonality::GNU_CXX)
      .Case("__gxx_personality_sj0", EHPersonality::GNU_CXX_SjLj)
      .Case("__gcc_personality_v0", EHPersonality::GNU_C)
      .Case("__gcc_personality_seh0", EHPersonality::GNU_C)
      .Case("__gcc_personality_sj0", EHPersonality::GNU_C_SjLj)
      .Case("__objc_personality_v0", EHPersonality::GNU_ObjC)
      .Case("_except_handler3", EHPersonality::MSVC_X86SEH)
      .Case("_except_handler4", EHPersonality::MSVC_X86SEH)
      .Case("__C_specific_handler", EHPersonality::MSVC_TableSEH)
      .Case("__CxxFrameHandler3", EHPersonality::MSVC_CXX)
      .Case("ProcessCLRException", EHPersonality::CoreCLR)
      .Case("rust_eh_personality", EHPersonality::Rust)
      .Case("__gxx_wasm_personality_v0", EHPersonality::Wasm_CXX)
      .Case("__xlcxx_personality_v1", EHPersonality::XL_CXX)
      .Case("__zos_cxx_personality_v2", EHPersonality::ZOS_CXX)
      .Default(EHPersonality::Unknown);
}

StringRef llvm::getEHPersonalityName(EHPersonality Pers) {
  switch (Pers) {
  case EHPersonality::GNU_Ada:
    return "__gnat_eh_personality";
  case EHPersonality::GNU_CXX:
    return "__gxx_personality_v0";
  case EHPersonality::GNU_CXX_SjLj:
    return "__gxx_personality_sj0";
  case EHPersonality::GNU_C:
    return "__gcc_personality_v0";
  case EHPersonality::GNU_C_SjLj:
    return "__gcc_personality_sj0";
  case EHPersonality::GNU_ObjC:
    return "__objc_personality_v0";
  case EHPersonality::MSVC_X86SEH:
    return "_except_handler3";
  case EHPersonality::MSVC_TableSEH:
    return "__C_specific_handler";
  case EHPersonality::MSVC_CXX:
    return "__CxxFrameHandler3";
  case EHPersonality::CoreCLR:
    return "ProcessCLRException";
  case EHPersonality::Rust:
    return "rust_eh_personality";
  case EHPersonality::Wasm_CXX:
    return "__gxx_wasm_personality_v0";
  case EHPersonality::XL_CXX:
    return "__xlcxx_personality_v1";
  case EHPersonality::ZOS_CXX:
    return "__zos_cxx_personality_v2";
  case EHPersonality::Unknown:
    llvm_unreachable("Unknown EHPersonality!");
  }

  llvm_unreachable("Invalid EHPersonality!");
}

EHPersonality llvm::getDefaultEHPersonality(const Triple &T) {
  if (T.isPS5())
    return EHPersonality::GNU_CXX;
  else
    return EHPersonality::GNU_C;
}

bool llvm::canSimplifyInvokeNoUnwind(const Function *F) {
  EHPersonality Personality = classifyEHPersonality(F->getPersonalityFn());
  // We can't simplify any invokes to nounwind functions if the personality
  // function wants to catch asynch exceptions.  The nounwind attribute only
  // implies that the function does not throw synchronous exceptions.

  // Cannot simplify CXX Personality under AsynchEH
  const llvm::Module *M = (const llvm::Module *)F->getParent();
  bool EHa = M->getModuleFlag("eh-asynch");
  return !EHa && !isAsynchronousEHPersonality(Personality);
}

DenseMap<BasicBlock *, ColorVector> llvm::colorEHFunclets(Function &F) {
  // 工作队列，存储待处理的（基本块，当前颜色）对
  SmallVector<std::pair<BasicBlock *, BasicBlock *>, 16> Worklist;
  BasicBlock *EntryBlock = &F.getEntryBlock();  // 获取函数的入口基本块
  DenseMap<BasicBlock *, ColorVector> BlockColors;  // 存储基本块到颜色集合的映射

  // 构建颜色映射表，将每个基本块映射到其所属的"颜色集"。
  // 对任意基本块B，其"颜色"表示需要直接包含B或其副本的funclet集合
  // （"直接包含"区别于在嵌套funclet中的"间接包含"）。
  //
  // 注意：尽管catchswitch并非严格意义上的funclet，但在着色过程中仍被视为属于自身的funclet。
  //
  // Build up the color map, which maps each block to its set of 'colors'.
  // For any block B the "colors" of B are the set of funclets F (possibly
  // including a root "funclet" representing the main function) such that
  // F will need to directly contain B or a copy of B (where the term "directly
  // contain" is used to distinguish from being "transitively contained" in
  // a nested funclet).
  //
  // Note: Despite not being a funclet in the truest sense, a catchswitch is
  // considered to belong to its own funclet for the purposes of coloring.

  DEBUG_WITH_TYPE("win-eh-prepare-coloring",
                  dbgs() << "\nColoring funclets for " << F.getName() << "\n");

  // 初始化：从入口块开始，初始颜色为入口块自身（代表主函数上下文）
  Worklist.push_back({EntryBlock, EntryBlock});

  while (!Worklist.empty()) {
    BasicBlock *Visiting;
    BasicBlock *Color;

    // 获取待处理块及其当前颜色
    std::tie(Visiting, Color) = Worklist.pop_back_val();
    DEBUG_WITH_TYPE("win-eh-prepare-coloring",
                    dbgs() << "Visiting " << Visiting->getName() << ", "
                           << Color->getName() << "\n");

    // 检查当前块是否为异常处理入口（EHPad）
    Instruction *VisitingHead = Visiting->getFirstNonPHI();
    if (VisitingHead->isEHPad()) {
      // 若是EHPad（catchswitch/cleanuppad/catchpad等），则创建新颜色域
      // 该块作为自身funclet的入口点
      // Mark this funclet head as a member of itself.
      Color = Visiting;
    }

    // 将当前颜色添加到该基本块的颜色集合
    // Note that this is a member of the given color.
    ColorVector &Colors = BlockColors[Visiting];
    if (!is_contained(Colors, Color)) {
      // 记录新颜色
      Colors.push_back(Color);
    } else {
      // 颜色已存在则跳过后续处理（避免循环）
      continue;
    }

    DEBUG_WITH_TYPE("win-eh-prepare-coloring",
                    dbgs() << "  Assigned color \'" << Color->getName()
                           << "\' to block \'" << Visiting->getName()
                           << "\'.\n");

    // 处理后继块的颜色继承

    BasicBlock *SuccColor = Color;  // 默认继承当前颜色
    Instruction *Terminator = Visiting->getTerminator();

    // 特殊处理catchret指令（异常处理返回）
    if (auto *CatchRet = dyn_cast<CatchReturnInst>(Terminator)) {
      Value *ParentPad = CatchRet->getCatchSwitchParentPad();
      if (isa<ConstantTokenNone>(ParentPad)) {
        // 无父funclet时返回主函数上下文（入口块）
        SuccColor = EntryBlock;
      } else {
        // 获取父funclet所在的基本块作为新颜色
        SuccColor = cast<Instruction>(ParentPad)->getParent();
      }
    }

    // 遍历所有后继块，赋予继承的颜色并加入工作队列
    for (BasicBlock *Succ : successors(Visiting))
      Worklist.push_back({Succ, SuccColor});
  }

  // 返回完成的着色映射
  return BlockColors;
}
