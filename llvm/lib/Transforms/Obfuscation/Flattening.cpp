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

#include "llvm/Transforms/Obfuscation/Flattening.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Constants.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
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
struct FlatteningContext {
  /// 一个随机密钥，用于打乱 case 值以增加反混淆难度
  char ScramblingKey[16];

  /// 存储原始的基本块
  vector<BasicBlock *> OrigBb;

  BasicBlock *FirstBasicBlock;

  /// 主循环入口块
  BasicBlock *LoopEntry;

  /// 主循环结束块
  BasicBlock *LoopEnd;

  /// 用于加载 switch 变量的指令
  LoadInst *Load;

  BasicBlock *SwDefault;

  /*
   它被添加到 loopEntry 基本块中，创建的 switch 指令，例如：
   switch i64 %switchVar14, label %switchDefault [
   ]
   */
  SwitchInst *SwitchI;
  // switch 变量（状态变量）
  AllocaInst *SwitchVar;

  IntegerType *IntType;
};

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

private:
  bool initFlatteningContext(
      Function *const F, FlatteningContext &FlatteningCtx);

  /// 初始化原基本块列表。
  /// @return 初始化成功则返回 true，否则返回 false
  inline bool initOrigBasicBlockList(
      Function *const F, FlatteningContext &FlatteningCtx);

  /// 为 loopEntry 基本块创建 switch 命令。
  inline void createSwitchForLoopEntry(
      Function *const F, FlatteningContext &FlatteningCtx);

  /// 直接跳转转成间接跳转。
  /// 遍历基本块，基本块的终止指令 直接跳转到基本块 改为 跳转到loopEntry后再做switch判断。
  inline void directBrToIndirect(
      Function *const F, FlatteningContext &FlatteningCtx);
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

bool Flattening::initFlatteningContext(
    Function *const F, FlatteningContext &FlatteningCtx) {

  // SCRAMBLER: 初始化一个随机密钥，用于打乱 case 值以增加反混淆难度
  llvm::cryptoutils->get_bytes(FlatteningCtx.ScramblingKey, 16);
  // END OF SCRAMBLER
  const char *const ScramblingKey = FlatteningCtx.ScramblingKey;

  // 获取函数第一个基本块指针
  const Function::iterator Tmp = F->begin();  //++tmp;
  BasicBlock *const FirstBasicBlock = &*Tmp;
  outs() << "函数第一个基本块:" << (*FirstBasicBlock) << "\n\n";
  FlatteningCtx.FirstBasicBlock = FirstBasicBlock;


  // 获取上下文和整型类型（根据指针大小决定是 32 位还是 64 位）
  LLVMContext &Ctx = F->getContext();
  IntegerType * IntType = Type::getInt32Ty(Ctx);
  if (PointerSize == 8) {
    IntType = Type::getInt64Ty(Ctx);
  }
  FlatteningCtx.IntType = IntType;


  // 初始化原基本块列表
  const bool InitOrigSuccess = initOrigBasicBlockList(F, FlatteningCtx);
  if (!InitOrigSuccess) {
    // 初始化失败
    return false;
  }

  // 删除 第一个基本块 的最后一条指令，准备插入新的控制流结构。
  // Remove jump
  FirstBasicBlock->getTerminator()->eraseFromParent();

  /*
   创建并在 第一个基本块 最后插入 switch 控制变量。
   例如：%switchVar = alloca i64, align 8
   */
  // Create switch variable and set as it
  FlatteningCtx.SwitchVar = new AllocaInst(
      IntType, 0, "switchVar", FirstBasicBlock);

  /*
   创建并在 第一个基本块 最后插入 store 命令。
   例如：store i64 5723693947865877014, ptr %switchVar, align 8
   */
  if (PointerSize == 8) {
    new StoreInst(
        ConstantInt::get(IntType,
                         llvm::cryptoutils->scramble64(
                             0, ScramblingKey)),
        FlatteningCtx.SwitchVar, FirstBasicBlock);
  } else {
    new StoreInst(
        ConstantInt::get(IntType,
                         llvm::cryptoutils->scramble32(
                             0, ScramblingKey)),
        FlatteningCtx.SwitchVar, FirstBasicBlock);
  }

  // 创建主循环结构：loopEntry 和 loopEnd
  // Create main loop
  FlatteningCtx.LoopEntry = BasicBlock::Create(
      F->getContext(), "loopEntry", F, FirstBasicBlock);
  FlatteningCtx.LoopEnd = BasicBlock::Create(
      F->getContext(), "loopEnd", F, FirstBasicBlock);

  /*
   在 loopEntry 的最后插入命令：插入的是加载 switch 用到的变量。插入前基本块是空的。
   例如：%switchVar14 = load i64, ptr %switchVar, align 8
   */
  FlatteningCtx.Load = new LoadInst(
      IntType, FlatteningCtx.SwitchVar, "switchVar",
      FlatteningCtx.LoopEntry);

  // 将原来的 第一个基本块 移到 loopEntry 前面
  // Move first BB on top
  FirstBasicBlock->moveBefore(FlatteningCtx.LoopEntry);

  return true;
}

bool Flattening::flatten(Function *const F, const ObfOpt& Opt) {
  // 预处理：将函数中的 switch 指令降级为一系列比较和跳转指令
  // Lower switch
  FunctionPass *const Lower = createLegacyLowerSwitchPass();
  Lower->runOnFunction(*F);

  FlatteningContext FlatteningCtx = {};
  // 初始化平台化上下文
  const bool InitFlatteningCtxSuccess = initFlatteningContext(
      F, FlatteningCtx);

  if (!InitFlatteningCtxSuccess) {
    return false;
  }

  BasicBlock *const LoopEntry = FlatteningCtx.LoopEntry;
  BasicBlock *const LoopEnd = FlatteningCtx.LoopEnd;
  BasicBlock *const FirstBasicBlock = FlatteningCtx.FirstBasicBlock;

  // 第一个基本块 最后插入 br 指令跳转到 loopEntry，例如：br label %loopEntry
  BranchInst::Create(LoopEntry, FirstBasicBlock);

  // loopEnd 跳回 loopEntry，构成循环。例如：br label %loopEntry
  // loopEnd jump to loopEntry
  BranchInst::Create(LoopEntry, LoopEnd);

  // 创建 switchDefault 基本块，它是默认 case 块所跳转的地方，它插入到 LoopEnd 之后。
  FlatteningCtx.SwDefault = BasicBlock::Create(
      F->getContext(), "switchDefault", F, LoopEnd);
  // switchDefault 最后插入跳转到 loopEnd 的指令，例如：br label %loopEnd
  BranchInst::Create(LoopEnd, FlatteningCtx.SwDefault);

  // 为 loopEntry 基本块创建 switch 命令
  createSwitchForLoopEntry(F, FlatteningCtx);

  // 直接跳转转成间接跳转
  directBrToIndirect(F, FlatteningCtx);

  outs() << "[" << TAG <<
      "] ----------- 将指令计算的虚拟寄存器（SSA 形式的变量）降级到堆栈（即分配栈内存存储其值） -----------\n"
      "函数:" << F->getName() << '\n';
  // 修复栈结构（可能涉及异常处理或调试信息等）
  fixStack(F);

  // 再次运行 LowerSwitch Pass 优化生成的 switch 结构
  Lower->runOnFunction(*F);
  delete(Lower);

  return true;
}

bool Flattening::initOrigBasicBlockList(
    Function *const F, FlatteningContext &FlatteningCtx) {
  vector<BasicBlock *> &OrigBb = FlatteningCtx.OrigBb;

  BasicBlock *const FirstBasicBlock = FlatteningCtx.FirstBasicBlock;

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
    outs() << "只有一个基本块，无需平坦化\n\n";
    return false;
  }

  // 移除第一个基本块（通常为主入口），后面会重新安排流程
  // Remove first BB
  OrigBb.erase(OrigBb.begin());

  // 如果第一个基本块以条件分支结束，则拆分它以便插入控制流结构
  BranchInst *Br = NULL;
  if (isa<BranchInst>(FirstBasicBlock->getTerminator())) {
    Br = cast<BranchInst>(FirstBasicBlock->getTerminator());
  }

  if ((Br != NULL && Br->isConditional()) ||
      FirstBasicBlock->getTerminator()->getNumSuccessors() > 1) {
    // TODO 没有执行到这里过，需要构建相应的例子执行到此处

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

  return true;
}

void Flattening::createSwitchForLoopEntry(
    Function *const F, FlatteningContext &FlatteningCtx) {
  vector<BasicBlock *>& OrigBb = FlatteningCtx.OrigBb;
  BasicBlock *const LoopEntry = FlatteningCtx.LoopEntry;
  BasicBlock *const LoopEnd = FlatteningCtx.LoopEnd;
  const char *const ScramblingKey = FlatteningCtx.ScramblingKey;

  /*
   loopEntry 最后插入 switch 指令，然后设置它的条件为 load 值（即 switchVar 的值）
   Create switch instruction itself and set condition

   语句执行后：
    switch label %entry, label %switchDefault [
    ]
    */
  SwitchInst *const SwitchI = SwitchInst::Create(
      &*F->begin(), FlatteningCtx.SwDefault, 0, LoopEntry);
  FlatteningCtx.SwitchI = SwitchI;

  /*
   语句执行后：
   switch i64 %switchVar14, label %switchDefault [
   ]
   */
  SwitchI->setCondition(FlatteningCtx.Load);

  // 删除函数入口块(entry)的跳转，并让它跳转到 loopEntry
  // TODO 这是没有必要的，因为此时终止指令已经是是 跳转到 loopEntry 的指令
  // Remove branch jump from 1st BB and make a jump to the while
  F->begin()->getTerminator()->eraseFromParent();
  BranchInst::Create(LoopEntry, &*F->begin());

  // 将所有原始基本块加入 switch 的 case 中(第一个基本块不会被办了到，因为上面把第一个)
  // Put all BB in the switch
  for (vector<BasicBlock *>::iterator B = OrigBb.begin(); B != OrigBb.end();
       ++B) {
    // 目标块
    BasicBlock *const DestBB = *B;
    ConstantInt *NumCase = NULL;

    // 将该基本块移动到 loopEnd 前面（仅视觉上顺序调整）
    // Move the BB inside the switch (only visual, no code logic)
    DestBB->moveBefore(LoopEnd);

    // 添加对应的 case 分支，值被打乱过。例如：i64 -3761430131291445899
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

    /*
     添加后 case 跳转到目标块。添加后举例：
     switch i64 %switchVar14, label %switchDefault [
      i64 -3761430131291445899, label %SwConvNodeBlock_1_
     ]
     */
    SwitchI->addCase(NumCase, DestBB);
  }

  /*
   上面循环执行完成后，switch 举例：
    switch i64 %switchVar14, label %switchDefault [
      i64 -9068860717773574370, label %SwConvNodeBlock_1_
      i64 -9068860718768112474, label %SwConvNodeBlock_2_11
      i64 -9068860719814512285, label %SwConvLeafBlock_3_9
      i64 -9068860717911456551, label %SwConvLeafBlock_3_7
      ......
      i64 -9068860717544530469, label %sw.bb
      i64 -9068860717742850501, label %sw.bb2
      ......
      i64 -9068860717718176324, label %if.then
      i64 -9068860718702902671, label %if.else
      i64 -9068860718179539988, label %NewDefault
      i64 -9068860718325703097, label %sw.default
      i64 -9068860718244552267, label %return
    ]
   */
}

void Flattening::directBrToIndirect(
    Function *const F, FlatteningContext &FlatteningCtx) {
  vector<BasicBlock *>& OrigBb = FlatteningCtx.OrigBb;
  BasicBlock *const LoopEnd = FlatteningCtx.LoopEnd;
  LoadInst *const Load = FlatteningCtx.Load;
  IntegerType *const IntType = FlatteningCtx.IntType;
  SwitchInst *const SwitchI = FlatteningCtx.SwitchI;
  const char *const ScramblingKey = FlatteningCtx.ScramblingKey;

  outs() << "[" << TAG <<
      "] ------------------- 遍历函数基本块 -------------------\n"
      "基本块的终止指令 直接跳转到基本块 改为 跳转到loopEntry后再做switch判断\n"
      "函数:" << F->getName() << "\n\n";

  // 用于加密跳转值的“秘钥”
  ConstantInt *const MySecret = ConstantInt::get(IntType, 0, true);

  // 修改每个基本块的终止指令，使其更新 switchVar 并跳转到 loopEnd
  // Recalculate switchVar
  for (vector<BasicBlock *>::iterator B = OrigBb.begin(); B != OrigBb.end();
       ++B) {
    BasicBlock *const CurBB = *B;

    const unsigned NumSuccessors = CurBB->getTerminator()->getNumSuccessors();

    outs() << "基本块:" << CurBB->getName()
           << ",后继数量:" << NumSuccessors << "\n";

    // 跳过无后续基本块的 Ret 指令
    // Ret BB
    if (NumSuccessors == 0) {
      outs() << "无后续基本块，跳过\n\n";
      continue;
    }

    /*
     例如:
     br label %return
     br i1 %Pivot13, label %SwConvNodeBlock_2_, label %SwConvNodeBlock_2_11
     */
    Instruction *const CurBBOldTerminator = CurBB->getTerminator();

    // 处理非条件跳转
    // If it's a non-conditional jump
    if (NumSuccessors == 1) {
      // 获取后继块并删除终结指令
      // Get successor and delete terminator
      BasicBlock *const Succ = CurBB->getTerminator()->getSuccessor(0);

      // 查找目标基本块对应的 case 值。例如：i64 8029005816011552985
      // Get next case
      ConstantInt *NumCase = SwitchI->findCaseDest(Succ);

      outs() << "终止指令(删除前):" << (*CurBBOldTerminator)
             << "\n后继:" << Succ->getName() << ",Case变量:";
      if (NumCase == nullptr) {
        outs() << "null";
      } else {
        outs() << (*NumCase);
      }

      // 擦除的指令例如：br label %return
      CurBB->getTerminator()->eraseFromParent();

      // 如果找不到，默认使用最后一个 case 值（被打乱）。例如：
      // 如果下一个 case 是默认 case (switchDefault)
      if (NumCase == nullptr) {
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

        outs() << "\n下一个是默认Case:" << (*NumCase);
      }

      /*
       计算新值：newNumCase = MySecret - (-numCase)。将计算指令插入到基本块最后
       例如：
         X ：i64 6538152691947866857
         NewNumCase：%27 = sub i64 0, 6538152691947866857
       */
      // numCase = MySecret - (MySecret - numCase)
      // X = MySecret - numCase
      Constant *X = ConstantExpr::getSub(MySecret, NumCase);
      // 值插入到基本块最后，例如：
      Value *const NewNumCase = BinaryOperator::Create(
          Instruction::Sub, MySecret, X, "", CurBB);

      /*
       更新 switchVar 并跳转到 loopEnd，指令插入到 CurBB 基本块最后。
       store 指令：store i64 %27, ptr %switchVar, align 8
       br 指令：br label %loopEnd
       */
      // Update switchVar and jump to the end of loop
      new StoreInst(NewNumCase, Load->getPointerOperand(), CurBB);
      BranchInst::Create(LoopEnd, CurBB);

      outs() << "\n\n";
      continue;
    }

    // 处理条件跳转（如 if-else）
    // If it's a conditional jump
    if (NumSuccessors == 2) {
      /*
       获取下一个 case 分支。例如：
        NumCaseTrue:i64 -3309989841140684037
        NumCaseFalse:i64 -3309989842549744837
       */
      // Get next cases
      BasicBlock *const Succ0 = CurBBOldTerminator->getSuccessor(0);
      BasicBlock *const Succ1 = CurBBOldTerminator->getSuccessor(1);
      ConstantInt *NumCaseTrue = SwitchI->findCaseDest(Succ0);
      ConstantInt *NumCaseFalse = SwitchI->findCaseDest(Succ1);

      outs() << "终止指令(删除前):" << (*CurBBOldTerminator)
             << "\n后继True:" << Succ0->getName() << ",Case变量:";
      if (NumCaseTrue == nullptr) {
        outs() << "null";
      } else {
        outs() << (*NumCaseTrue);
      }
      outs() << "\n后继False:" << Succ1->getName() << ",Case变量:";
      if (NumCaseFalse == nullptr) {
        outs() << "null";
      } else {
        outs() << (*NumCaseFalse);
      }

      /*
       如果找不到对应 case，使用最后一个 case 值（被打乱）。例如：

       */
      // Check if next case == default case (switchDefault)
      if (NumCaseTrue == nullptr) {
        // 例如：
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
        outs() << "\n下一个是默认CaseTrue:" << (*NumCaseTrue);
      }

      if (NumCaseFalse == nullptr) {
        // 例如：
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
        outs() << "\n下一个是默认CaseFalse:" << (*NumCaseFalse);
      }

      // case 值加密：0 - 真正的case值
      Constant *X, *Y;
      X = ConstantExpr::getSub(MySecret, NumCaseTrue);
      Y = ConstantExpr::getSub(MySecret, NumCaseFalse);

      /*
       创建 case 值计算指令，插入到终止指令之前，case 值被下面创建的 Select 指令用到
       计算是为了解密 case 值，MySecret 是 0，0 减去 case 值就对上面的加密进行了解密
       */

      // 例如：%4 = sub i64 0, -5721412848776271138
      Value *NewNumCaseTrue = BinaryOperator::Create(
          Instruction::Sub, MySecret, X, "", CurBB->getTerminator());
      // 例如：%5 = sub i64 0, -5721412850363480502
      Value *NewNumCaseFalse = BinaryOperator::Create(
          Instruction::Sub, MySecret, Y, "", CurBB->getTerminator());

      /*
       创建 SelectInst 指令，插入到终止指令之前，指令用到了上面创建的 case 值。
       Br 指令例如：br i1 %Pivot13, label %SwConvNodeBlock_2_, label %SwConvNodeBlock_2_11
       select 指令例如：%6 = select i1 %Pivot13, i64 %4, i64 %5
       */
      // Create a SelectInst
      BranchInst *const Br = cast<BranchInst>(CurBB->getTerminator());
      SelectInst *Sel = SelectInst::Create(
          Br->getCondition(), NewNumCaseTrue, NewNumCaseFalse,
          "", CurBB->getTerminator());

      // 基本块 删除终结指令
      // Erase terminator
      CurBB->getTerminator()->eraseFromParent();

      /*
       更新 switchVar 并跳转到 loopEnd，指令插入到 CurBB 基本块最后。

       Load->getPointerOperand() 例如：%switchVar = alloca i64, align 8
       store 指令例如：store i64 %6, ptr %switchVar, align 8
       br 指令例如：br label %loopEnd
       */
      // Update switchVar and jump to the end of loop
      new StoreInst(Sel, Load->getPointerOperand(), CurBB);
      BranchInst::Create(LoopEnd, CurBB);

      outs() << "\n\n";
      continue;
    }
  }
}

const char * const Flattening::TAG = "控制流平坦混淆";
char Flattening::ID = 0;

static RegisterPass<Flattening> X("flattening", "Call graph flattening");
FunctionPass *llvm::createFlatteningPass(
    unsigned PointerSize, ObfuscationOptions *ArgsOptions) {
  return new Flattening(PointerSize, ArgsOptions);
}
