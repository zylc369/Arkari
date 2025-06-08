#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/EHPersonalities.h"
#include "llvm/IR/NoFolder.h"

// 判断一个指令是否在当前基本块之外被使用（即值是否“逃逸”出当前块）
// 如果该值的使用不在同一个基本块中，或者是一个PHI节点，则认为它逃逸了。
// Shamefully borrowed from ../Scalar/RegToMem.cpp :(
bool valueEscapes(Instruction *Inst) {
  // 获取该指令所在的基本块
  BasicBlock *BB = Inst->getParent();
  for (Value::use_iterator UI = Inst->use_begin(), E = Inst->use_end(); UI != E;
       ++UI) {
    Instruction *I = cast<Instruction>(*UI);
    // 使用不在本块 或者 是 PHI 节点
    if (I->getParent() != BB || isa<PHINode>(I)) {
      // 值逃逸
      return true;
    }
  }
  return false;
}

// 将寄存器变量降级为栈变量，并处理 PHI 节点
void fixStack(Function *const F) {
  // 存放需要降级的 PHI 节点
  // Try to remove phi node and demote reg to stack
  std::vector<PHINode *>     TmpPhi;
  // 存放需要降级为栈的寄存器变量
  std::vector<Instruction *> TmpReg;
  // 函数入口块
  BasicBlock *               const BbEntry = &*F->begin();

  do {
    TmpPhi.clear();
    TmpReg.clear();

    // 遍历函数中的所有基本块和指令
    for (Function::iterator I = F->begin(); I != F->end(); ++I) {

      for (BasicBlock::iterator J = I->begin(); J != I->end(); ++J) {

        // 如果是 PHI 指令
        if (isa<PHINode>(J)) {
          PHINode *const Phi = cast<PHINode>(J);
          // 加入 PHI 列表
          TmpPhi.push_back(Phi);
          continue;
        }

        // 如果不是入口块中的 alloca 指令，并且该指令逃逸了（跨块使用）
        const bool IsAllocaInst = isa<AllocaInst>(J);
        const bool IsEntryBB = J->getParent() == BbEntry;
        const bool IsValueEscapes = valueEscapes(&*J);
        const bool IsUsedOutsideOfBlock = J->isUsedOutsideOfBlock(&*I);

        outs() << "IsAllocaInst:" << IsAllocaInst << ",IsEntryBB:" << IsEntryBB
               << ",IsValueEscapes:" << IsValueEscapes
               << ",IsUsedOutsideOfBlock:" << IsUsedOutsideOfBlock << "\n\n";

        if (!(IsAllocaInst && IsEntryBB) &&
            (IsValueEscapes || IsUsedOutsideOfBlock)) {
          // 加入寄存器列表
          TmpReg.push_back(&*J);
          continue;
        }
      }
    }

    // 将收集到的寄存器变量降级为栈变量
    for (unsigned int I = 0; I != TmpReg.size(); ++I) {
      DemoteRegToStack(*TmpReg.at(I));
    }

    // 将收集到的 PHI 节点降级为栈变量
    for (unsigned int I = 0; I != TmpPhi.size(); ++I) {
      DemotePHIToStack(TmpPhi.at(I));
    }

    // 循环直到没有更多可降级内容
  } while (TmpReg.size() != 0 || TmpPhi.size() != 0);
}

// 修复异常处理调用，添加 funclet operand bundle
CallBase* fixEH(CallBase* CB) {
  // 获取调用所在的块
  auto *const BB = CB->getParent();
  if (!BB) {
    // 如果没有父块，直接返回
    return CB;
  }

  // 获取函数
  auto *const Fn = BB->getParent();
  // 如果函数没有 personality 函数 或者 不支持 scoped EH，则不处理
  if (!Fn || !Fn->hasPersonalityFn()) {
    return CB;
  }

  const Constant *const ThePersonalityFn = Fn->getPersonalityFn();
  const EHPersonality ThePers = classifyEHPersonality(ThePersonalityFn);
  if (!isScopedEHPersonality(ThePers)) {
    return CB;
  }

  // 给函数中的每个块分配颜色（funclet 所属关系）
  const auto BlockColors = colorEHFunclets(*Fn);
  // 查找当前块的颜色
  const auto BBColor = BlockColors.find(BB);
  if (BBColor == BlockColors.end()) {
    // 没有找到对应颜色信息
    return CB;
  }
  const auto& ColorVec = BBColor->getSecond();
  assert(ColorVec.size() == 1 && "non-unique color for block!");

  // 获取对应的 funclet 块
  auto *const EHBlock = ColorVec.front();
  // 必须是 EHPad 类型
  if (!EHBlock || !EHBlock->isEHPad()) {
    return CB;
  }
  // 获取第一个非 PHI 的指令作为 funclet 入口
  auto *const EHPad = EHBlock->getFirstNonPHI();

  // 创建 funclet operand bundle
  const OperandBundleDef OB("funclet", EHPad);
  // 添加 operand bundle 到调用
  auto *NewCall = CallBase::addOperandBundle(CB, LLVMContext::OB_funclet, OB, CB);
  // 复制元数据
  NewCall->copyMetadata(*CB);
  // 替换所有使用
  CB->replaceAllUsesWith(NewCall);
  // 删除旧调用
  CB->eraseFromParent();
  return NewCall;
}

/**
 * 将函数内所有指令拆开转换为低级指令
 *
 * @param F 函数
 */
void LowerConstantExpr(Function &F) {
  // 待处理的指令集合
  SmallPtrSet<Instruction *, 8> WorkList;

  // 收集包含 ConstantExpr 操作数的指令
  for (inst_iterator It = inst_begin(F), E = inst_end(F); It != E; ++It) {
    Instruction *I = &*It;

    // 跳过异常处理相关指令
    if (isa<LandingPadInst>(I) || isa<CatchPadInst>(I) || isa<
          CatchSwitchInst>(I) || isa<CatchReturnInst>(I))
      continue;
    if (auto *II = dyn_cast<IntrinsicInst>(I)) {
      if (II->getIntrinsicID() == Intrinsic::eh_typeid_for) {
        // 跳过特定 intrinsic
        continue;
      }
    }

    // 检查操作数是否是 ConstantExpr
    for (unsigned int i = 0; i < I->getNumOperands(); ++i) {
      if (isa<ConstantExpr>(I->getOperand(i)))
        // 加入工作队列
        WorkList.insert(I);
    }
  }

  while (!WorkList.empty()) {
    auto         It = WorkList.begin();
    Instruction *I = *It;
    WorkList.erase(*It);

    if (PHINode *PHI = dyn_cast<PHINode>(I)) {
      // 处理 PHI 节点中的 ConstantExpr
      for (unsigned int i = 0; i < PHI->getNumIncomingValues(); ++i) {
        Instruction *TI = PHI->getIncomingBlock(i)->getTerminator();
        if (ConstantExpr *CE = dyn_cast<
          ConstantExpr>(PHI->getIncomingValue(i))) {
          Instruction *NewInst = CE->getAsInstruction();
          // 插入新指令
          NewInst->insertBefore(TI);
          // 替换 PHI 输入值
          PHI->setIncomingValue(i, NewInst);
          // 加入队列继续处理
          WorkList.insert(NewInst);
        }
      }
    } else {
      // 处理普通指令中的 ConstantExpr
      for (unsigned int i = 0; i < I->getNumOperands(); ++i) {
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(I->getOperand(i))) {
          /*
           I 例如：
           %0 = load ptr, ptr getelementptr inbounds (%struct.StructTest, ptr @dec__ZL11struct_test, i32 0, i32 1), align 8

           CE 例如：ptr getelementptr (%struct.StructTest, ptr @dec__ZL11struct_test, i32 0, i32 1)
           NewInst 例如：<badref> = getelementptr inbounds %struct.StructTest, ptr @_ZL11struct_test, i32 0, i32 1
           */
          Instruction *NewInst = CE->getAsInstruction();

          /*
           插入新指令。插入后返回值有了名字：
           %0 = getelementptr inbounds %struct.StructTest, ptr @_ZL11struct_test, i32 0, i32 1
           */
          NewInst->insertBefore(I);

          // 替换使用。替换后例如：%1 = load ptr, ptr %0, align 8
          I->replaceUsesOfWith(CE, NewInst);

          // 对 NewInst 继续做降低操作
          WorkList.insert(NewInst);
        }
      }
    }
  }
}

// 展开常量表达式，将其替换为真正的指令
bool expandConstantExpr(Function &F) {
  // 是否发生改变
  bool                Changed = false;
  // 上下文
  LLVMContext &       Ctx = F.getContext();
  // 不进行折叠的 IR 构建器
  IRBuilder<NoFolder> IRB(Ctx);

  // 遍历所有基本块
  for (auto &BB : F) {
    // 遍历所有指令
    for (auto &I : BB) {
      // 忽略以下类型指令
      if (I.isEHPad() || isa<AllocaInst>(&I) || isa<IntrinsicInst>(&I) ||
        isa<SwitchInst>(&I) || I.isAtomic()) {
        continue;
      }
      auto *const CI = dyn_cast<CallInst>(&I);
      auto *const GEP = dyn_cast<GetElementPtrInst>(&I);
      auto IsPhi = isa<PHINode>(&I);
      // 确定插入位置：如果是 PHI 节点则放在入口块的第一个可插入位置，否则就放在当前指令前
      auto InsertPt = IsPhi
        ? F.getEntryBlock().getFirstInsertionPt()
        : I.getIterator();
      // 遍历操作数
      for (unsigned i = 0; i < I.getNumOperands(); ++i) {
        if (CI && CI->isBundleOperand(i)) {
          // 跳过 operand bundle
          continue;
        }
        if (GEP && (i < 2 || GEP->getSourceElementType()->isStructTy())) {
          // GEP 特殊处理，跳过部分索引
          continue;
        }

        auto *const Opr = I.getOperand(i);
        if (auto *CEP = dyn_cast<ConstantExpr>(Opr)) {
          // 设置插入点
          IRB.SetInsertPoint(InsertPt);
          // 将 ConstantExpr 转换为指令
          auto *const CEPInst = CEP->getAsInstruction();
          // 插入到 IR 中
          IRB.Insert(CEPInst);
          // 替换操作数
          I.setOperand(i, CEPInst);
          // 标记已更改
          Changed = true;
        }
      }
    }
  }
  return Changed;
}
