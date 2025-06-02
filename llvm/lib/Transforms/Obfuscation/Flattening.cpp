//===- Flattening.cpp - Flattening Obfuscation pass------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the flattening pass
// 这个文件实现了控制流平坦化（Control Flow Flattening）混淆 Pass。
// 通过将函数内的所有基本块放入一个 switch-case 结构中，
// 并在一个主循环中根据 switch 变量选择执行路径，从而打乱原有的控制流结构。
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Constants.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Flattening.h"
#include "llvm/Transforms/Obfuscation/LegacyLowerSwitch.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/Utils.h"

#define DEBUG_TYPE "flattening"

using namespace std;
using namespace llvm;

// 统计信息：被平坦化的函数数量
// Stats
STATISTIC(Flattened, "Functions flattened");

namespace {
/**
 * 过程相关控制流平坦混淆
 */
struct Flattening : public FunctionPass {
  static const char * const TAG;

  // 指针大小（32 或 64 位）
  unsigned PointerSize;
  // Pass 标识符
  static char ID;  // Pass identification, replacement for typeid
  
  // 混淆选项参数
  ObfuscationOptions *ArgsOptions;
  // 加密工具实例
  CryptoUtils RandomEngine;

  Flattening(unsigned PointerSize, ObfuscationOptions *ArgsOptions)
      : FunctionPass(ID) {
    this->PointerSize = PointerSize;
    this->ArgsOptions = ArgsOptions;
  }

  bool runOnFunction(Function &F) override;
  bool flatten(Function *F, const ObfOpt& Opt);
};
} // namespace

bool Flattening::runOnFunction(Function &F) {
  Function *Tmp = &F;
  bool Result = false;
  // 判断是否对当前函数启用控制流平坦化混淆
  // Do we obfuscate
  const auto Opt = ArgsOptions->toObfuscate(ArgsOptions->flaOpt(), &F);
  if (!Opt.isEnabled()) {
    return Result;
  }

  // 执行实际的平坦化操作
  if (flatten(Tmp, Opt)) {
    // 成功处理后统计加一
      ++Flattened;
      Result = true;
    }

  return Result;
}

bool Flattening::flatten(Function *const F, const ObfOpt& Opt) {
  // 存储原始的基本块
  vector<BasicBlock *> OrigBb;
  // 主循环入口块
  BasicBlock *LoopEntry;
  // 主循环结束块
  BasicBlock *LoopEnd;
  // 用于加载 switch 变量的指令
  LoadInst *Load;
  // 创建的 switch 指令
  SwitchInst *SwitchI;
  // switch 变量（状态变量）
  AllocaInst *SwitchVar;

  // SCRAMBLER: 初始化一个随机密钥，用于打乱 case 值以增加反混淆难度
  // SCRAMBLER
  char ScramblingKey[16];
  llvm::cryptoutils->get_bytes(ScramblingKey, 16);
  // END OF SCRAMBLER

  // 预处理：将函数中的 switch 指令降级为一系列比较和跳转指令
  // Lower switch
  FunctionPass *const Lower = createLegacyLowerSwitchPass();
  Lower->runOnFunction(*F);

  outs() << "[" << TAG <<
      "] ------------------- 遍历函数基本块 -------------------\n"
      "函数:" << F->getName() << '\n';
  // 收集所有原始基本块并检查是否包含 invoke 指令（目前不支持）
  // Save all original BB
  for (Function::iterator I = F->begin(); I != F->end(); ++I) {
    BasicBlock *Tmp = &*I;
    OrigBb.push_back(Tmp);

    BasicBlock *Bb = &*I;
    if (isa<InvokeInst>(Bb->getTerminator())) {
      // 如果存在 invoke 指令则放弃混淆
      outs() << "存在 invoke 指令，放弃混淆。函数名:"
             << I->getName() << "\n\n";
      return false;
    }
  }

  // 如果只有一个基本块，无需平坦化
  // Nothing to flatten
  if (OrigBb.size() <= 1) {
    return false;
  }

  // 获取上下文和整型类型（根据指针大小决定是 32 位还是 64 位）
  LLVMContext &Ctx = F->getContext();
  IntegerType *IntType = Type::getInt32Ty(Ctx);
  if (PointerSize == 8) {
    IntType = Type::getInt64Ty(Ctx);
  }

  // 用于加密跳转值的“秘钥”
  Value *const MySecret = ConstantInt::get(IntType, 0, true);

  // 移除第一个基本块（通常为主入口），后面会重新安排流程
  // Remove first BB
  OrigBb.erase(OrigBb.begin());

  // 获取函数的第一个基本块作为插入点
  // Get a pointer on the first BB
  Function::iterator Tmp = F->begin();  //++tmp;
  BasicBlock *const FirstBasicBlock = &*Tmp;
  outs() << "函数第一个基本块:" << (*FirstBasicBlock) << "\n\n";

  // 如果第一个基本块以条件分支结束，则拆分它以便插入控制流结构
  BranchInst *Br = NULL;
  if (isa<BranchInst>(FirstBasicBlock->getTerminator())) {
    Br = cast<BranchInst>(FirstBasicBlock->getTerminator());
  }

  if ((Br != NULL && Br->isConditional()) ||
      FirstBasicBlock->getTerminator()->getNumSuccessors() > 1) {
    BasicBlock::iterator I = FirstBasicBlock->end();
        --I;

    if (FirstBasicBlock->size() > 1) {
      --I;
    }

    BasicBlock *TmpBb = FirstBasicBlock->splitBasicBlock(I, "first");
    outs() << "临时基本块:" << (*TmpBb) << "\n\n";
    outs() << "函数第一个基本块 2:" << (*FirstBasicBlock) << "\n\n";

    OrigBb.insert(OrigBb.begin(), TmpBb);
  }

  // 删除原入口块的最后一条指令，准备插入新的控制流结构
  // Remove jump
  FirstBasicBlock->getTerminator()->eraseFromParent();

  // 在插入点创建一个 switch 状态变量，并初始化为 0（经过打乱）
  // Create switch variable and set as it
  SwitchVar = new AllocaInst(
      IntType, 0, "switchVar", FirstBasicBlock);
  if (PointerSize == 8) {
    new StoreInst(
      ConstantInt::get(IntType,
        llvm::cryptoutils->scramble64(0, ScramblingKey)),
      SwitchVar, FirstBasicBlock);
  } else {
    new StoreInst(
      ConstantInt::get(IntType,
        llvm::cryptoutils->scramble32(0, ScramblingKey)),
      SwitchVar, FirstBasicBlock);
  }

  // 创建主循环结构：loopEntry 和 loopEnd
  // Create main loop
  LoopEntry = BasicBlock::Create(F->getContext(), "loopEntry", F, FirstBasicBlock);
  LoopEnd = BasicBlock::Create(F->getContext(), "loopEnd", F, FirstBasicBlock);

  // 在 loopEntry 中加载 switch 变量
  Load = new LoadInst(IntType, SwitchVar, "switchVar", LoopEntry);

  // 将原来的第一个基本块移到 loopEntry 前面，并跳转到 loopEntry
  // Move first BB on top
  FirstBasicBlock->moveBefore(LoopEntry);
  BranchInst::Create(LoopEntry, FirstBasicBlock);

  // loopEnd 跳回 loopEntry，构成循环
  // loopEnd jump to loopEntry
  BranchInst::Create(LoopEntry, LoopEnd);

  // 创建默认 case 块（switchDefault），跳转到 loopEnd
  BasicBlock *const SwDefault =
      BasicBlock::Create(F->getContext(), "switchDefault", F, LoopEnd);
  BranchInst::Create(LoopEnd, SwDefault);

  // 创建 switch 指令并设置条件为 load（即 switchVar 的值）
  // Create switch instruction itself and set condition
  SwitchI = SwitchInst::Create(&*F->begin(), SwDefault, 0, LoopEntry);
  SwitchI->setCondition(Load);

  // 删除函数入口块的跳转，并让它跳转到 loopEntry
  // Remove branch jump from 1st BB and make a jump to the while
  F->begin()->getTerminator()->eraseFromParent();

  BranchInst::Create(LoopEntry, &*F->begin());

  // 将所有原始基本块加入 switch 的 case 中
  // Put all BB in the switch
  for (vector<BasicBlock *>::iterator B = OrigBb.begin(); B != OrigBb.end();
       ++B) {
    BasicBlock *const I = *B;
    ConstantInt *NumCase = NULL;

    // 将该基本块移动到 loopEnd 前面（仅视觉上顺序调整）
    // Move the BB inside the switch (only visual, no code logic)
    I->moveBefore(LoopEnd);

    // 添加对应的 case 分支，值被打乱过
    // Add case to switch
    if (PointerSize == 8) {
      NumCase = cast<ConstantInt>(ConstantInt::get(
          SwitchI->getCondition()->getType(),
          llvm::cryptoutils->scramble64(SwitchI->getNumCases(), ScramblingKey)));
    } else {
      NumCase = cast<ConstantInt>(ConstantInt::get(
        SwitchI->getCondition()->getType(),
        llvm::cryptoutils->scramble32(SwitchI->getNumCases(), ScramblingKey)));
    }
    SwitchI->addCase(NumCase, I);
  }

  ConstantInt *Zero = ConstantInt::get(IntType, 0);
  // 修改每个基本块的终止指令，使其更新 switchVar 并跳转到 loopEnd
  // Recalculate switchVar
  for (vector<BasicBlock *>::iterator B = OrigBb.begin(); B != OrigBb.end();
       ++B) {
    BasicBlock *I = *B;
    ConstantInt *NumCase = NULL;

    // 跳过无后续基本块的 Ret 指令
    // Ret BB
    if (I->getTerminator()->getNumSuccessors() == 0) {
      continue;
    }

    // 处理非条件跳转
    // If it's a non-conditional jump
    if (I->getTerminator()->getNumSuccessors() == 1) {
      // Get successor and delete terminator
      BasicBlock *const Succ = I->getTerminator()->getSuccessor(0);
      I->getTerminator()->eraseFromParent();

      // 查找目标基本块对应的 case 值
      // Get next case
      NumCase = SwitchI->findCaseDest(Succ);

      // 如果找不到，默认使用最后一个 case 值（被打乱）
      // If next case == default case (switchDefault)
      if (NumCase == NULL) {
        if (PointerSize == 8) {
          NumCase = cast<ConstantInt>(
              ConstantInt::get(SwitchI->getCondition()->getType(),
                               llvm::cryptoutils->scramble64(
                                   SwitchI->getNumCases() - 1, ScramblingKey)));
        } else {
          NumCase = cast<ConstantInt>(
            ConstantInt::get(SwitchI->getCondition()->getType(),
              llvm::cryptoutils->scramble32(
                SwitchI->getNumCases() - 1, ScramblingKey)));
        }
      }

      // 计算新值：newNumCase = MySecret - (-numCase)
      // numCase = MySecret - (MySecret - numCase)
      // X = MySecret - numCase
      Constant *X = ConstantExpr::getSub(Zero, NumCase);
      Value *const NewNumCase = BinaryOperator::Create(
          Instruction::Sub, MySecret, X, "", I);

      // 更新 switchVar 并跳转到 loopEnd
      // Update switchVar and jump to the end of loop
      new StoreInst(NewNumCase, Load->getPointerOperand(), I);
      BranchInst::Create(LoopEnd, I);
      continue;
    }

    // 处理条件跳转（如 if-else）
    // If it's a conditional jump
    if (I->getTerminator()->getNumSuccessors() == 2) {
      // Get next cases
      ConstantInt *NumCaseTrue =
          SwitchI->findCaseDest(I->getTerminator()->getSuccessor(0));
      ConstantInt *NumCaseFalse =
          SwitchI->findCaseDest(I->getTerminator()->getSuccessor(1));

      // 如果找不到对应 case，使用最后一个 case 值（被打乱）
      // Check if next case == default case (switchDefault)
      if (NumCaseTrue == NULL) {
        if (PointerSize == 8) {
          NumCaseTrue = cast<ConstantInt>(
              ConstantInt::get(SwitchI->getCondition()->getType(),
                               llvm::cryptoutils->scramble64(
                                   SwitchI->getNumCases() - 1, ScramblingKey)));
        } else {
          NumCaseTrue = cast<ConstantInt>(
            ConstantInt::get(SwitchI->getCondition()->getType(),
              llvm::cryptoutils->scramble32(
                SwitchI->getNumCases() - 1, ScramblingKey)));
        }
      }

      if (NumCaseFalse == NULL) {
        if (PointerSize == 8) {
          NumCaseFalse = cast<ConstantInt>(
              ConstantInt::get(SwitchI->getCondition()->getType(),
                               llvm::cryptoutils->scramble64(
                                   SwitchI->getNumCases() - 1, ScramblingKey)));
        } else {
          NumCaseFalse = cast<ConstantInt>(
            ConstantInt::get(SwitchI->getCondition()->getType(),
              llvm::cryptoutils->scramble32(
                SwitchI->getNumCases() - 1, ScramblingKey)));
        }
      }

      // 构造 Select 指令来动态选择要跳转的 case 值
      Constant *X, *Y;
      X = ConstantExpr::getSub(Zero, NumCaseTrue);
      Y = ConstantExpr::getSub(Zero, NumCaseFalse);
      Value *NewNumCaseTrue = BinaryOperator::Create(Instruction::Sub, MySecret, X, "", I->getTerminator());
      Value *NewNumCaseFalse = BinaryOperator::Create(Instruction::Sub, MySecret, Y, "", I->getTerminator());

      // Create a SelectInst
      BranchInst *br = cast<BranchInst>(I->getTerminator());
      SelectInst *sel =
          SelectInst::Create(br->getCondition(), NewNumCaseTrue, NewNumCaseFalse, "",
                             I->getTerminator());

      // Erase terminator
      I->getTerminator()->eraseFromParent();

      // 更新 switchVar 并跳转到 loopEnd
      // Update switchVar and jump to the end of loop
      new StoreInst(sel, Load->getPointerOperand(), I);
      BranchInst::Create(LoopEnd, I);
      continue;
    }
  }

  // 修复栈结构（可能涉及异常处理或调试信息等）
  fixStack(F);

  // 再次运行 LowerSwitch Pass 优化生成的 switch 结构
  Lower->runOnFunction(*F);
  delete(Lower);

  return true;
}

const char * const Flattening::TAG = "控制流平坦混淆";
char Flattening::ID = 0;

static RegisterPass<Flattening> X("flattening", "Call graph flattening");
FunctionPass *llvm::createFlatteningPass(
    unsigned PointerSize, ObfuscationOptions *ArgsOptions) {
  return new Flattening(PointerSize, ArgsOptions);
}
