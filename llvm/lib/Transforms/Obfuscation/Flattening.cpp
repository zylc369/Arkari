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
#include "llvm/Transforms/Obfuscation/Flattening.h"
#include "llvm/Transforms/Obfuscation/LegacyLowerSwitch.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/CryptoUtils.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"

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
  unsigned pointerSize;
  // Pass 标识符
  static char ID;  // Pass identification, replacement for typeid
  
  // 混淆选项参数
  ObfuscationOptions *ArgsOptions;
  // 加密工具实例
  CryptoUtils RandomEngine;

  Flattening(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  bool runOnFunction(Function &F) override;
  bool flatten(Function *f, const ObfOpt& opt);
};
}

bool Flattening::runOnFunction(Function &F) {
  Function *tmp = &F;
  bool result = false;
  // 判断是否对当前函数启用控制流平坦化混淆
  // Do we obfuscate
  const auto opt = ArgsOptions->toObfuscate(ArgsOptions->flaOpt(), &F);
  if (!opt.isEnabled()) {
    return result;
  }

  // 执行实际的平坦化操作
  if (flatten(tmp, opt)) {
    // 成功处理后统计加一
      ++Flattened;
      result = true;
    }

  return result;
}

bool Flattening::flatten(Function *const f, const ObfOpt& opt) {
  // 存储原始的基本块
  vector<BasicBlock *> origBB;
  // 主循环入口块
  BasicBlock *loopEntry;
  // 主循环结束块
  BasicBlock *loopEnd;
  // 用于加载 switch 变量的指令
  LoadInst *load;
  // 创建的 switch 指令
  SwitchInst *switchI;
  // switch 变量（状态变量）
  AllocaInst *switchVar;

  // SCRAMBLER: 初始化一个随机密钥，用于打乱 case 值以增加反混淆难度
  // SCRAMBLER
  char scrambling_key[16];
  llvm::cryptoutils->get_bytes(scrambling_key, 16);
  // END OF SCRAMBLER

  // 预处理：将函数中的 switch 指令降级为一系列比较和跳转指令
  // Lower switch
  FunctionPass *lower = createLegacyLowerSwitchPass();
  lower->runOnFunction(*f);

  outs() << "[" << TAG <<
      "] ------------------- 遍历函数基本块 -------------------\n"
      "函数:" << f->getName() << '\n';
  // 收集所有原始基本块并检查是否包含 invoke 指令（目前不支持）
  // Save all original BB
  for (Function::iterator i = f->begin(); i != f->end(); ++i) {
    BasicBlock *tmp = &*i;
    origBB.push_back(tmp);

    BasicBlock *bb = &*i;
    if (isa<InvokeInst>(bb->getTerminator())) {
      // 如果存在 invoke 指令则放弃混淆
      outs() << "存在 invoke 指令，放弃混淆。函数名:"
             << i->getName() << "\n\n";
      return false;
    }
  }

  // 如果只有一个基本块，无需平坦化
  // Nothing to flatten
  if (origBB.size() <= 1) {
    return false;
  }

  // 获取上下文和整型类型（根据指针大小决定是 32 位还是 64 位）
  LLVMContext &Ctx = f->getContext();
  IntegerType *intType = Type::getInt32Ty(Ctx);
  if (pointerSize == 8) {
    intType = Type::getInt64Ty(Ctx);
  }

  // 用于加密跳转值的“秘钥”
  Value *const MySecret = ConstantInt::get(intType, 0, true);

  // 移除第一个基本块（通常为主入口），后面会重新安排流程
  // Remove first BB
  origBB.erase(origBB.begin());

  // 获取函数的第一个基本块作为插入点
  // Get a pointer on the first BB
  Function::iterator tmp = f->begin();  //++tmp;
  BasicBlock *const firstBasicBlock = &*tmp;
  outs() << "函数第一个基本块:" << (*firstBasicBlock) << "\n\n";

  // 如果第一个基本块以条件分支结束，则拆分它以便插入控制流结构
  BranchInst *br = NULL;
  if (isa<BranchInst>(firstBasicBlock->getTerminator())) {
    br = cast<BranchInst>(firstBasicBlock->getTerminator());
  }

  if ((br != NULL && br->isConditional()) ||
      firstBasicBlock->getTerminator()->getNumSuccessors() > 1) {
    BasicBlock::iterator i = firstBasicBlock->end();
        --i;

    if (firstBasicBlock->size() > 1) {
      --i;
    }

    BasicBlock *tmpBB = firstBasicBlock->splitBasicBlock(i, "first");
    outs() << "临时基本块:" << (*tmpBB) << "\n\n";
    outs() << "函数第一个基本块 2:" << (*firstBasicBlock) << "\n\n";

    origBB.insert(origBB.begin(), tmpBB);
  }

  // 删除原入口块的最后一条指令，准备插入新的控制流结构
  // Remove jump
  firstBasicBlock->getTerminator()->eraseFromParent();

  // 在插入点创建一个 switch 状态变量，并初始化为 0（经过打乱）
  // Create switch variable and set as it
  switchVar = new AllocaInst(
      intType, 0, "switchVar", firstBasicBlock);
  if (pointerSize == 8) {
    new StoreInst(
      ConstantInt::get(intType,
        llvm::cryptoutils->scramble64(0, scrambling_key)),
      switchVar, firstBasicBlock);
  } else {
    new StoreInst(
      ConstantInt::get(intType,
        llvm::cryptoutils->scramble32(0, scrambling_key)),
      switchVar, firstBasicBlock);
  }

  // 创建主循环结构：loopEntry 和 loopEnd
  // Create main loop
  loopEntry = BasicBlock::Create(f->getContext(), "loopEntry", f, firstBasicBlock);
  loopEnd = BasicBlock::Create(f->getContext(), "loopEnd", f, firstBasicBlock);

  // 在 loopEntry 中加载 switch 变量
  load = new LoadInst(intType, switchVar, "switchVar", loopEntry);

  // 将原来的第一个基本块移到 loopEntry 前面，并跳转到 loopEntry
  // Move first BB on top
  firstBasicBlock->moveBefore(loopEntry);
  BranchInst::Create(loopEntry, firstBasicBlock);

  // loopEnd 跳回 loopEntry，构成循环
  // loopEnd jump to loopEntry
  BranchInst::Create(loopEntry, loopEnd);

  // 创建默认 case 块（switchDefault），跳转到 loopEnd
  BasicBlock *swDefault =
      BasicBlock::Create(f->getContext(), "switchDefault", f, loopEnd);
  BranchInst::Create(loopEnd, swDefault);

  // 创建 switch 指令并设置条件为 load（即 switchVar 的值）
  // Create switch instruction itself and set condition
  switchI = SwitchInst::Create(&*f->begin(), swDefault, 0, loopEntry);
  switchI->setCondition(load);

  // 删除函数入口块的跳转，并让它跳转到 loopEntry
  // Remove branch jump from 1st BB and make a jump to the while
  f->begin()->getTerminator()->eraseFromParent();

  BranchInst::Create(loopEntry, &*f->begin());

  // 将所有原始基本块加入 switch 的 case 中
  // Put all BB in the switch
  for (vector<BasicBlock *>::iterator b = origBB.begin(); b != origBB.end();
       ++b) {
    BasicBlock *i = *b;
    ConstantInt *numCase = NULL;

    // 将该基本块移动到 loopEnd 前面（仅视觉上顺序调整）
    // Move the BB inside the switch (only visual, no code logic)
    i->moveBefore(loopEnd);

    // 添加对应的 case 分支，值被打乱过
    // Add case to switch
    if (pointerSize == 8) {
      numCase = cast<ConstantInt>(ConstantInt::get(
          switchI->getCondition()->getType(),
          llvm::cryptoutils->scramble64(switchI->getNumCases(), scrambling_key)));
    } else {
      numCase = cast<ConstantInt>(ConstantInt::get(
        switchI->getCondition()->getType(),
        llvm::cryptoutils->scramble32(switchI->getNumCases(), scrambling_key)));
    }
    switchI->addCase(numCase, i);
  }

  ConstantInt *Zero = ConstantInt::get(intType, 0);
  // 修改每个基本块的终止指令，使其更新 switchVar 并跳转到 loopEnd
  // Recalculate switchVar
  for (vector<BasicBlock *>::iterator b = origBB.begin(); b != origBB.end();
       ++b) {
    BasicBlock *i = *b;
    ConstantInt *numCase = NULL;

    // 跳过无后续基本块的 Ret 指令
    // Ret BB
    if (i->getTerminator()->getNumSuccessors() == 0) {
      continue;
    }

    // 处理非条件跳转
    // If it's a non-conditional jump
    if (i->getTerminator()->getNumSuccessors() == 1) {
      // Get successor and delete terminator
      BasicBlock *succ = i->getTerminator()->getSuccessor(0);
      i->getTerminator()->eraseFromParent();

      // 查找目标基本块对应的 case 值
      // Get next case
      numCase = switchI->findCaseDest(succ);

      // 如果找不到，默认使用最后一个 case 值（被打乱）
      // If next case == default case (switchDefault)
      if (numCase == NULL) {
        if (pointerSize == 8) {
          numCase = cast<ConstantInt>(
              ConstantInt::get(switchI->getCondition()->getType(),
                               llvm::cryptoutils->scramble64(
                                   switchI->getNumCases() - 1, scrambling_key)));
        } else {
          numCase = cast<ConstantInt>(
            ConstantInt::get(switchI->getCondition()->getType(),
              llvm::cryptoutils->scramble32(
                switchI->getNumCases() - 1, scrambling_key)));
        }
      }

      // 计算新值：newNumCase = MySecret - (-numCase)
      // numCase = MySecret - (MySecret - numCase)
      // X = MySecret - numCase
      Constant *X = ConstantExpr::getSub(Zero, numCase);
      Value *newNumCase = BinaryOperator::Create(Instruction::Sub, MySecret, X, "", i);

      // 更新 switchVar 并跳转到 loopEnd
      // Update switchVar and jump to the end of loop
      new StoreInst(newNumCase, load->getPointerOperand(), i);
      BranchInst::Create(loopEnd, i);
      continue;
    }

    // 处理条件跳转（如 if-else）
    // If it's a conditional jump
    if (i->getTerminator()->getNumSuccessors() == 2) {
      // Get next cases
      ConstantInt *numCaseTrue =
          switchI->findCaseDest(i->getTerminator()->getSuccessor(0));
      ConstantInt *numCaseFalse =
          switchI->findCaseDest(i->getTerminator()->getSuccessor(1));

      // 如果找不到对应 case，使用最后一个 case 值（被打乱）
      // Check if next case == default case (switchDefault)
      if (numCaseTrue == NULL) {
        if (pointerSize == 8) {
          numCaseTrue = cast<ConstantInt>(
              ConstantInt::get(switchI->getCondition()->getType(),
                               llvm::cryptoutils->scramble64(
                                   switchI->getNumCases() - 1, scrambling_key)));
        } else {
          numCaseTrue = cast<ConstantInt>(
            ConstantInt::get(switchI->getCondition()->getType(),
              llvm::cryptoutils->scramble32(
                switchI->getNumCases() - 1, scrambling_key)));
        }
      }

      if (numCaseFalse == NULL) {
        if (pointerSize == 8) {
          numCaseFalse = cast<ConstantInt>(
              ConstantInt::get(switchI->getCondition()->getType(),
                               llvm::cryptoutils->scramble64(
                                   switchI->getNumCases() - 1, scrambling_key)));
        } else {
          numCaseFalse = cast<ConstantInt>(
            ConstantInt::get(switchI->getCondition()->getType(),
              llvm::cryptoutils->scramble32(
                switchI->getNumCases() - 1, scrambling_key)));
        }
      }

      // 构造 Select 指令来动态选择要跳转的 case 值
      Constant *X, *Y;
      X = ConstantExpr::getSub(Zero, numCaseTrue);
      Y = ConstantExpr::getSub(Zero, numCaseFalse);
      Value *newNumCaseTrue = BinaryOperator::Create(Instruction::Sub, MySecret, X, "", i->getTerminator());
      Value *newNumCaseFalse = BinaryOperator::Create(Instruction::Sub, MySecret, Y, "", i->getTerminator());

      // Create a SelectInst
      BranchInst *br = cast<BranchInst>(i->getTerminator());
      SelectInst *sel =
          SelectInst::Create(br->getCondition(), newNumCaseTrue, newNumCaseFalse, "",
                             i->getTerminator());

      // Erase terminator
      i->getTerminator()->eraseFromParent();

      // 更新 switchVar 并跳转到 loopEnd
      // Update switchVar and jump to the end of loop
      new StoreInst(sel, load->getPointerOperand(), i);
      BranchInst::Create(loopEnd, i);
      continue;
    }
  }

  // 修复栈结构（可能涉及异常处理或调试信息等）
  fixStack(f);

  // 再次运行 LowerSwitch Pass 优化生成的 switch 结构
  lower->runOnFunction(*f);
  delete(lower);

  return true;
}

const char * const Flattening::TAG = "控制流平坦混淆";
char Flattening::ID = 0;

static RegisterPass<Flattening> X("flattening", "Call graph flattening");
FunctionPass *llvm::createFlatteningPass(unsigned pointerSize, ObfuscationOptions *argsOptions) {
  return new Flattening(pointerSize, argsOptions);
}
