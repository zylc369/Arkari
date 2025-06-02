//===- LowerSwitch.cpp - Eliminate Switch instructions --------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The LowerSwitch transformation rewrites switch instructions with a sequence
// of branches, which allows targets to get away with not implementing the
// switch instruction until it is convenient.
//
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Obfuscation/LegacyLowerSwitch.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iterator>
#include <limits>
#include <vector>

using namespace llvm;

#define DEBUG_TYPE "lower-switch"

namespace {

  struct IntRange {
    int64_t Low, High;
  };

} // end anonymous namespace

// Return true iff R is covered by Ranges.
static bool IsInRanges(const IntRange &R,
                       const std::vector<IntRange> &Ranges) {
  // Note: Ranges must be sorted, non-overlapping and non-adjacent.

  // Find the first range whose High field is >= R.High,
  // then check if the Low field is <= R.Low. If so, we
  // have a Range that covers R.
  auto I = std::lower_bound(
      Ranges.begin(), Ranges.end(), R,
      [](const IntRange &A, const IntRange &B) { return A.High < B.High; });
  return I != Ranges.end() && I->Low <= R.Low;
}

namespace {

  /// 将所有 SwitchInst 指令替换为链式分支指令。
  /// Replace all SwitchInst instructions with chained branch instructions.
  class LowerSwitch : public FunctionPass {
  public:
    // Pass identification, replacement for typeid
    static char ID;

    LowerSwitch() : FunctionPass(ID) {
      //initializeLowerSwitchPass(*PassRegistry::getPassRegistry());
    }

    bool runOnFunction(Function &F) override;

    struct CaseRange {
      ConstantInt* Low;
      ConstantInt* High;

      /// Case的后继基本块
      BasicBlock* SuccessorBB;

      CaseRange(ConstantInt *Low, ConstantInt *High, BasicBlock *SuccessorBB)
          : Low(Low), High(High), SuccessorBB(SuccessorBB) {}
    };

    using CaseVector = std::vector<CaseRange>;
    using CaseItr = std::vector<CaseRange>::iterator;

  private:
    static const char * const TAG;

    void processSwitchInst(SwitchInst *SI, SmallPtrSetImpl<BasicBlock*> &DeleteList);

    BasicBlock *switchConvert(
        const unsigned Level, const char *const Tag,
        const CaseItr Begin, const CaseItr End,
        ConstantInt *const LowerBound, ConstantInt *const UpperBound,
        Value *const SwConditionVal,
        BasicBlock *const Predecessor, BasicBlock *const OrigBlock,
        BasicBlock *const Default,
        const std::vector<IntRange> &UnreachableRanges);

    BasicBlock *newLeafBlock(
        const char *const BasicBlockNamePrefix,
        CaseRange &Leaf, Value *const SwConditionVal,
        BasicBlock *const OrigBlock,BasicBlock *const Default);

    unsigned Clusterify(CaseVector &Cases, SwitchInst *SI);
  };

  /// 用于对向量中的 switch case 值进行排序的比较函数
  /// 警告：各 case 范围必须互不相交！
  ///
  /// The comparison function for sorting the switch case values in the vector.
  /// WARNING: Case ranges should be disjoint!
  struct CaseCmp {
    bool operator()(const LowerSwitch::CaseRange& C1,
                    const LowerSwitch::CaseRange& C2) {
      // 获取C1的下界值
      const ConstantInt* CI1 = cast<const ConstantInt>(C1.Low);
      // 获取C2的上界值
      const ConstantInt* CI2 = cast<const ConstantInt>(C2.High);
      return CI1->getValue().slt(CI2->getValue());
    }
  };

} // end anonymous namespace

char LowerSwitch::ID = 0;
const char * const LowerSwitch::TAG = "Switch指令转换";

// Publicly exposed interface to pass...
//char &llvm::LowerSwitchID = LowerSwitch::ID;

//INITIALIZE_PASS(LowerSwitch, "lowerswitch",
//                "Lower SwitchInst's to branches", false, false)

// createLowerSwitchPass - Interface to this file...
FunctionPass *llvm::createLegacyLowerSwitchPass() {
  return new LowerSwitch();
}

bool LowerSwitch::runOnFunction(Function &F) {
  bool Changed = false;
  SmallPtrSet<BasicBlock*, 8> DeleteList; // 待删除基本块集合

  // 遍历函数中的每个基本块
  for (Function::iterator I = F.begin(), E = F.end(); I != E; ) {
    // 递增迭代器（避免处理新增块）
    BasicBlock *Cur = &*I++; // Advance over block so we don't traverse new blocks

    // 如果当前块在待删除列表中，跳过处理
    // If the block is a dead Default block that will be deleted later, don't
    // waste time processing it.
    if (DeleteList.count(Cur))
      continue;

    // 检查基本块终止指令是否为SwitchInst（switch语句）
    if (SwitchInst *SI = dyn_cast<SwitchInst>(Cur->getTerminator())) {
      Changed = true;
      // 转换该 switch 指令为分支链
      processSwitchInst(SI, DeleteList);
    }
  }

  // 清理所有待删除基本块
  for (BasicBlock* BB: DeleteList) {
    DeleteDeadBlock(BB);  // 删除死代码块
  }

  return Changed;
}

// 调试用：打印 CaseVector 内容
/// Used for debugging purposes.
LLVM_ATTRIBUTE_USED
static raw_ostream &operator<<(raw_ostream &O,
                               const LowerSwitch::CaseVector &C) {
  O << "[";

  // 打印每个 case 的范围 [Low - High]
  for (LowerSwitch::CaseVector::const_iterator B = C.begin(),
         E = C.end(); B != E; ) {
    O << *B->Low << " -" << *B->High;
    if (++B != E) O << ", ";
  }

  return O << "]";
}

/// 更新PHI节点中"switch语句"基本块(OrigBB)的第一个出现位置为"新"基本块(NewBB)。其余出现位置将：
///
/// 1) 由后续对此函数的调用更新。当多个case具有相同值时，switch语句可能有多个出边指向同一基本块。
/// 转换switch语句后，这些入边现在来自多个不同基本块。
/// 2) 如果后续入值现在共享相同case则被移除（即多个出边被合并为一个）。这需要保持phi值的数量
/// 与到SuccBB的分支数量一致。
///
/// Update the first occurrence of the "switch statement" BB in the PHI
/// node with the "new" BB. The other occurrences will:
///
/// 1) Be updated by subsequent calls to this function.  Switch statements may
/// have more than one outcoming edge into the same BB if they all have the same
/// value. When the switch statement is converted these incoming edges are now
/// coming from multiple BBs.
/// 2) Removed if subsequent incoming values now share the same case, i.e.,
/// multiple outcome edges are condensed into one. This is necessary to keep the
/// number of phi values equal to the number of branches to SuccBB.
static void fixPhis(BasicBlock *SuccBB, BasicBlock *OrigBB, BasicBlock *NewBB,
                    unsigned NumMergedCases) {
  // 遍历所有 PHI 节点
  for (BasicBlock::iterator I = SuccBB->begin(),
                            IE = SuccBB->getFirstNonPHI()->getIterator();
       I != IE; ++I) {
    PHINode *PN = cast<PHINode>(I);

    // 仅更新第一个匹配OrigBB的前驱块
    // Only update the first occurrence.
    unsigned Idx = 0, E = PN->getNumIncomingValues();
    unsigned LocalNumMergedCases = NumMergedCases;
    for (; Idx != E; ++Idx) {
      if (PN->getIncomingBlock(Idx) == OrigBB) {
        // 替换为新块
        PN->setIncomingBlock(Idx, NewBB);
        break;
      }
    }

    // 移除因 case 合并而产生的多余 OrigBB 前驱
    // Remove additional occurrences coming from condensed cases and keep the
    // number of incoming values equal to the number of branches to SuccBB.
    SmallVector<unsigned, 8> Indices;
    for (++Idx; LocalNumMergedCases > 0 && Idx < E; ++Idx)
      if (PN->getIncomingBlock(Idx) == OrigBB) {
        Indices.push_back(Idx);
        LocalNumMergedCases--;
      }

    // 按逆序删除以避免索引失效
    // Remove incoming values in the reverse order to prevent invalidating
    // *successive* index.
    for (unsigned III : llvm::reverse(Indices))
      PN->removeIncomingValue(III);
  }
}

/// 将 switch 语句转换为对 case 值的二分查找
/// 该函数递归构建这棵二分查找树。LowerBound 和 UpperBound 用于跟踪在调用栈中
/// 已被之前 switchConvert 调用生成的基本块检查过的Val值范围
///
/// Convert the switch statement into a binary lookup of the case values.
/// The function recursively builds this tree. LowerBound and UpperBound are
/// used to keep track of the bounds for Val that have already been checked by
/// a block emitted by one of the previous calls to switchConvert in the call
/// stack.
BasicBlock *
LowerSwitch::switchConvert(
    const unsigned Level, const char *const Tag,
    const CaseItr Begin, const CaseItr End,
    ConstantInt *const LowerBound, ConstantInt *const UpperBound,
    Value *const SwConditionVal,
    BasicBlock *const Predecessor,
    BasicBlock *const OrigBlock, BasicBlock *const Default,
    const std::vector<IntRange> &UnreachableRanges) {
  unsigned Size = End - Begin;

  // 基本情况：只有一个 case
  if (Size == 1) {
    // 如果当前case范围正好被上下界完全覆盖，则无需重复检查，因为边界条件已经隐含了这个信息
    // Check if the Case Range is perfectly squeezed in between
    // already checked Upper and Lower bounds. If it is then we can avoid
    // emitting the code that checks if the value actually falls in the range
    // because the bounds already tell us so.
    if (Begin->Low == LowerBound && Begin->High == UpperBound) {
      unsigned NumMergedCases = 0;
      if (LowerBound && UpperBound)
        NumMergedCases =
            UpperBound->getSExtValue() - LowerBound->getSExtValue();
      fixPhis(Begin->SuccessorBB, OrigBlock, Predecessor, NumMergedCases);
      return Begin->SuccessorBB;
    }
    // 创建叶节点
    return newLeafBlock(Tag, *Begin, SwConditionVal, OrigBlock, Default);
  }

  unsigned Mid = Size / 2;
  // 左子树
  std::vector<CaseRange> LHS(Begin, Begin + Mid);
  LLVM_DEBUG(dbgs() << "LHS: " << LHS << "\n");
  // 右子树
  std::vector<CaseRange> RHS(Begin + Mid, End);
  LLVM_DEBUG(dbgs() << "RHS: " << RHS << "\n");

  // 当前分割点
  const CaseRange &Pivot = *(Begin + Mid);
  LLVM_DEBUG(dbgs() << "Pivot ==> " << Pivot.Low->getValue() << " -"
                    << Pivot.High->getValue() << "\n");

  // 计算新的边界值
  // 注意 NewLowerBound 永远不会是最小整数值，因为它总是来自非最小 case 范围的计算
  // NewLowerBound here should never be the integer minimal value.
  // This is because it is computed from a case range that is never
  // the smallest, so there is always a case range that has at least
  // a smaller value.
  ConstantInt *const NewLowerBound = Pivot.Low;

  // 由于 NewLowerBound 不是最小可表示整数，这里安全地减 1 来获得新的上界
  // Because NewLowerBound is never the smallest representable integer
  // it is safe here to subtract one.
  ConstantInt *NewUpperBound = ConstantInt::get(NewLowerBound->getContext(),
                                                NewLowerBound->getValue() - 1);

  // 判断中间是否有不可达区间（可以简化比较）
  if (!UnreachableRanges.empty()) {
    // 检查左半部分最高值与新下界之间的间隙是否不可达
    // Check if the gap between LHS's highest and NewLowerBound is unreachable.
    int64_t GapLow = LHS.back().High->getSExtValue() + 1;
    int64_t GapHigh = NewLowerBound->getSExtValue() - 1;
    IntRange Gap = { GapLow, GapHigh };
    if (GapHigh >= GapLow && IsInRanges(Gap, UnreachableRanges))
      NewUpperBound = LHS.back().High;
  }

  // 调试输出
  LLVM_DEBUG(dbgs() << "LHS Bounds ==> "; if (LowerBound) {
    dbgs() << LowerBound->getSExtValue();
  } else { dbgs() << "NONE"; } dbgs() << " - "
                                      << NewUpperBound->getSExtValue() << "\n";
             dbgs() << "RHS Bounds ==> ";
             dbgs() << NewLowerBound->getSExtValue() << " - "; if (UpperBound) {
               dbgs() << UpperBound->getSExtValue() << "\n";
             } else { dbgs() << "NONE\n"; });

  // 创建新节点用于检查当前值是否小于基准值（pivot）
  // 分支逻辑：
  // - 若小于基准值，跳转到左侧分支
  // - 否则跳转到右侧分支
  // Create a new node that checks if the value is < pivot. Go to the
  // left branch if it is and right branch if not.
  Function *const F = OrigBlock->getParent();
  // 创建空基本块。例如：SwConvNodeBlock:                                  ; No predecessors!
  BasicBlock *const NewSwConvNodeBlock = BasicBlock::Create(
      SwConditionVal->getContext(), "SwConvNodeBlock");

  // 递归构建左、右子树
  BasicBlock *const LBranch = switchConvert(
      Level + 1, "Left", LHS.begin(), LHS.end(),
      LowerBound, NewUpperBound, SwConditionVal,
      NewSwConvNodeBlock, OrigBlock, Default, UnreachableRanges);
  BasicBlock *const RBranch = switchConvert(
      Level + 1, "Right", RHS.begin(), RHS.end(),
      NewLowerBound, UpperBound, SwConditionVal,
      NewSwConvNodeBlock, OrigBlock, Default, UnreachableRanges);

  outs() << "[switchConvert] ### Level:"
         << Level << ",Tag:" << Tag
         << "\n[LBranch]\n" << (*LBranch) << "\n[RBranch]\n" << (*RBranch)
         << "##############################\n\n";

  /*
   左树基本块 LBranch 举例：
   LeftSwConvLeafBlock:                              ; No predecessors!
    %SwitchLeaf = icmp eq i32 %conv1, 42
    br i1 %SwitchLeaf, label %sw.bb3, label %NewDefault

   右树基本块 RBranch 举例：
   RightSwConvLeafBlock:                             ; No predecessors!
    %SwitchLeaf5 = icmp eq i32 %conv1, 43
    br i1 %SwitchLeaf5, label %sw.bb, label %NewDefault

   左右树会在下面添加到基本块 NewSwConvNodeBlock 中
   */

  // 将新基本块插入到原块之后
  F->insert(++OrigBlock->getIterator(), NewSwConvNodeBlock);

  // 比较指令：Val < Pivot.Low。例如：%Pivot = icmp slt i32 %conv1, 45
  ICmpInst *const Comp = new ICmpInst(
      ICmpInst::ICMP_SLT, SwConditionVal, Pivot.Low, "Pivot");
  // 比较语句插入到基本块最后
  Comp->insertInto(NewSwConvNodeBlock, NewSwConvNodeBlock->end());

  // 添加条件跳转添加到新基本块最后
  BranchInst::Create(LBranch, RBranch, Comp, NewSwConvNodeBlock);

  /*
   插入后语句举例：
   SwConvNodeBlock:                                  ; No predecessors!
    %Pivot = icmp slt i32 %conv1, 43
    br i1 %Pivot, label %LeftSwConvLeafBlock, label %RightSwConvLeafBlock
   */

  outs() << "----------------------------------------------------------\n\n";
  return NewSwConvNodeBlock;
}

/// 为二分查找树创建新的叶子节点块。该块检查switch值是否等于当前case值，
/// 若不相等则跳转到默认分支。在树的这个位置，该值已不可能是其他有效case值，
/// 因此可以直接跳转到默认分支。
///
/// Create a new leaf block for the binary lookup tree. It checks if the
/// switch's value == the case's value. If not, then it jumps to the default
/// branch. At this point in the tree, the value can't be another valid case
/// value, so the jump to the "default" branch is warranted.
BasicBlock* LowerSwitch::newLeafBlock(
    const char *const BasicBlockNamePrefix,
    CaseRange& Leaf, Value *const SwConditionVal,
    BasicBlock *const OrigBlock, BasicBlock *const Default) {
  Function *const F = OrigBlock->getParent();
  std::string Name = BasicBlockNamePrefix;
  Name += "SwConvLeafBlock";
  BasicBlock *const NewLeaf = BasicBlock::Create(SwConditionVal->getContext(), Name);
  F->insert(++OrigBlock->getIterator(), NewLeaf);

  // 根据 Low 和 High 是否相等选择不同的比较方式
  // Emit comparison
  ICmpInst* Comp;
  if (Leaf.Low == Leaf.High) {
    // 单个值比较：Val == Low

    // 构建比较语句然后插入到 NewLeaf 基本块的最后。比较指令如：%SwitchLeaf = icmp eq i32 %conv1, 42
    // Make the seteq instruction...
    Comp = new ICmpInst(NewLeaf->end(), ICmpInst::ICMP_EQ, SwConditionVal,
                        Leaf.Low, "SwitchLeaf");
  } else {
    // 区间比较
    // Make range comparison
    if (Leaf.Low->isMinValue(true /*isSigned*/)) {
      // Val >= Min && Val <= Hi --> Val <= Hi
      Comp = new ICmpInst(NewLeaf->end(), ICmpInst::ICMP_SLE, SwConditionVal, Leaf.High,
                          "SwitchLeaf");
    } else if (Leaf.Low->isZero()) {
      // Val >= 0 && Val <= Hi --> Val <=u Hi
      Comp = new ICmpInst(NewLeaf->end(), ICmpInst::ICMP_ULE, SwConditionVal, Leaf.High,
                          "SwitchLeaf");
    } else {
      // 使用偏移量比较：V-Lo <=u Hi-Lo
      // Emit V-Lo <=u Hi-Lo
      Constant* NegLo = ConstantExpr::getNeg(Leaf.Low);
      Instruction* Add = BinaryOperator::CreateAdd(
          SwConditionVal, NegLo, SwConditionVal->getName()+".off",
                                                   NewLeaf);
      Constant *UpperBound = ConstantExpr::getAdd(NegLo, Leaf.High);
      Comp = new ICmpInst(NewLeaf->end(), ICmpInst::ICMP_ULE, Add, UpperBound,
                          "SwitchLeaf");
    }
  }

  // 条件跳转：满足则跳转到目标块，否则跳转到 default。指令构建后插入到 NewLeaf 基本块的最后
  // Make the conditional branch...
  BasicBlock *const Succ = Leaf.SuccessorBB;
  BranchInst::Create(Succ, Default, Comp, NewLeaf);

  // 更新目标块中的 PHI 节点
  // If there were any PHI nodes in this successor, rewrite one entry
  // from OrigBlock to come from NewLeaf.
  for (BasicBlock::iterator I = Succ->begin(); isa<PHINode>(I); ++I) {
    PHINode* PN = cast<PHINode>(I);
    // Remove all but one incoming entries from the cluster
    uint64_t Range = Leaf.High->getSExtValue() -
                     Leaf.Low->getSExtValue();
    // 移除多余的 OrigBlock 入口
    for (uint64_t J = 0; J < Range; ++J) {
      PN->removeIncomingValue(OrigBlock);
    }

    int BlockIdx = PN->getBasicBlockIndex(OrigBlock);
    assert(BlockIdx != -1 && "Switch didn't go to this successor??");
    // 替换为新块
    PN->setIncomingBlock((unsigned)BlockIdx, NewLeaf);
  }

  // 返回新的叶子基本块
  return NewLeaf;
}

/// 将简单的 Cases 列表转换为 CaseRange 列表
/// Transform simple list of Cases into list of CaseRange's.
unsigned LowerSwitch::Clusterify(CaseVector& Cases, SwitchInst *SI) {
  unsigned NumCmps = 0; // 记录最终需要的比较次数

  // 首先处理基本case（每个case单独存储）
  // Start with "simple" cases
  for (auto Case : SI->cases())
    Cases.push_back(CaseRange(Case.getCaseValue(), Case.getCaseValue(),
                              Case.getCaseSuccessor()));

  // 将所有 case 按照 Low 排序，便于后续合并相邻 case
  llvm::sort(Cases.begin(), Cases.end(), CaseCmp());

  // 合并相邻case形成连续区间
  // Merge case into clusters
  if (Cases.size() >= 2) {
    // 主迭代器（指向当前合并区间）
    CaseItr I = Cases.begin();

    for (CaseItr J = std::next(I), E = Cases.end(); J != E; ++J) {
      int64_t NextValue = J->Low->getSExtValue();     // 下一个case的整数值
      int64_t CurrentValue = I->High->getSExtValue(); // 当前区间的上限
      BasicBlock* NextBb = J->SuccessorBB;     // 下一个case的目标块
      BasicBlock* CurrentBb = I->SuccessorBB;  // 当前区间的目标块

      // 如果两个连续的 case 具有相同的跳转目标，则合并它们的区间
      // If the two neighboring cases go to the same destination, merge them
      // into a single case.
      assert(NextValue > CurrentValue && "Cases should be strictly ascending");
      if ((NextValue == CurrentValue + 1) && (CurrentBb == NextBb)) {
        I->High = J->High;    // 扩展当前区间上限
        // FIXME: Combine branch weights. 待优化：此处应合并分支权重
      } else if (++I != J) {  // 不满足合并条件时移动主迭代器
        *I = *J;  // 保留当前case（可能成为新区间的起点）
      }
    }

    // 清理合并后多余的case项
    Cases.erase(std::next(I), Cases.end());
  }

  // 计算比较次数：每个 range 需要两次比较（上下界：低、高），单个值只需一次
  for (CaseItr I=Cases.begin(), E=Cases.end(); I!=E; ++I, ++NumCmps) {
    if (I->Low != I->High) {  // 如果是区间case
      // 额外增加一次比较计数
      // A range counts double, since it requires two compares.
      ++NumCmps;
    }
  }

  // 返回总比较次数（用于后续优化决策）
  return NumCmps;
}

/// 将指定的switch指令替换为一组链式if-then指令，采用平衡二叉搜索结构
///
/// Replace the specified switch instruction with a sequence of chained if-then
/// insts in a balanced binary search.
void LowerSwitch::processSwitchInst(SwitchInst *SI,
                                    SmallPtrSetImpl<BasicBlock*> &DeleteList) {
  // 获取当前 SwitchInst 所在的基本块及其函数
  BasicBlock *const CurBlock = SI->getParent();
  BasicBlock *const OrigBlock = CurBlock;
  Function *const F = CurBlock->getParent();

  // 获取 switch 的条件值（即被 switch 的变量）。例如：%conv1 = sext i8 %3 to i32
  Value *const SwConditionVal = SI->getCondition();  // The value we are switching on...

  // 获取默认分支的目标基本块
  BasicBlock *Default = SI->getDefaultDest();
  if (!Default) {
    outs() << "[" << TAG << "] 暂不支持没有default的switch。函数名:\n"
           << F->getName() << ",基本块名:" << CurBlock->getName() <<  '\n';
    return;
  }

  // 如果当前块是不可达的（没有前驱或自循环），则标记为删除并返回
  // 不处理不可达块。如果有后继块包含phi节点，会导致这些phi节点缺失前驱
  // Don't handle unreachable blocks. If there are successors with phis, this
  // would leave them behind with missing predecessors.
  if ((CurBlock != &F->getEntryBlock() && pred_empty(CurBlock)) ||
      CurBlock->getSinglePredecessor() == CurBlock) {
    DeleteList.insert(CurBlock);
    return;
  }

  // 如果没有 case 分支，直接跳转到 default 块
  // If there is only the default destination, just branch.
  if (!SI->getNumCases()) {
    BranchInst::Create(Default, CurBlock);
    SI->eraseFromParent();
    return;
  }

  // 创建一个 CaseVector 来保存所有 case 的范围
  // Prepare cases vector.
  CaseVector Cases;
  // 合并相邻的 case 到 CaseRange 中
  unsigned NumCmps = Clusterify(Cases, SI);

  LLVM_DEBUG(dbgs() << "Clusterify finished. Total clusters: " << Cases.size()
                    << ". Total compares: " << NumCmps << "\n");
  LLVM_DEBUG(dbgs() << "Cases: " << Cases << "\n");
  // 防止未使用的警告
  (void)NumCmps;

  ConstantInt *LowerBound = nullptr;
  ConstantInt *UpperBound = nullptr;
  std::vector<IntRange> UnreachableRanges;

  // 如果默认块是 unreachable，则可以进行一些优化
  if (isa<UnreachableInst>(Default->getFirstNonPHIOrDbg())) {
    // 使边界紧密贴合 case 值的范围，因为我们知道传递给 switch 的值必定是某个 case 值
    // Make the bounds tightly fitted around the case value range, because we
    // know that the value passed to the switch must be exactly one of the case
    // values.
    assert(!Cases.empty());

    // 设置边界：只可能落在 case 范围内，不需要考虑其他情况
    LowerBound = Cases.front().Low;
    UpperBound = Cases.back().High;

    DenseMap<BasicBlock *, unsigned> Popularity;
    unsigned MaxPop = 0;
    BasicBlock *PopSucc = nullptr;

    // 构建不可达区间范围，便于后续优化比较逻辑
    IntRange R = {std::numeric_limits<int64_t>::min(),
                  std::numeric_limits<int64_t>::max()};
    UnreachableRanges.push_back(R);
    for (const auto &I : Cases) {
      int64_t Low = I.Low->getSExtValue();
      int64_t High = I.High->getSExtValue();

      IntRange &LastRange = UnreachableRanges.back();
      if (LastRange.Low == Low) {
        // 当前 Low 紧接上一段的开始，合并成一个连续段
        // There is nothing left of the previous range.
        UnreachableRanges.pop_back();
      } else {
        // 更新上一段的结尾为 Low - 1
        // Terminate the previous range.
        assert(Low > LastRange.Low);
        LastRange.High = Low - 1;
      }

      // 添加新的不可达区间 [High + 1, max]
      if (High != std::numeric_limits<int64_t>::max()) {
        UnreachableRanges.push_back(
            {High + 1, std::numeric_limits<int64_t>::max()});
      }

      // 统计每个目标块的流行度（出现次数）
      // Count popularity.
      int64_t N = High - Low + 1;
      unsigned &Pop = Popularity[I.SuccessorBB];
      if ((Pop += N) > MaxPop) {
        MaxPop = Pop;
        PopSucc = I.SuccessorBB;
      }
    }

    if (PopSucc) {

#ifndef NDEBUG
      // Debug 检查：确保不可达区间有序且不重叠
      /* UnreachableRanges should be sorted and the ranges non-adjacent. */
      for (auto I = UnreachableRanges.begin(), E = UnreachableRanges.end();
           I != E; ++I) {
        assert(I->Low <= I->High);
        auto Next = I + 1;
        if (Next != E) {
          assert(Next->Low > I->High);
        }
      }
#endif

      // 由于 switch 的默认块不可达，更新PHI节点（移除默认块的入口）
      // As the default block in the switch is unreachable, update the PHI nodes
      // (remove the entry to the default block) to reflect this.
      Default->removePredecessor(OrigBlock);

      // 将最流行的块作为新的默认块，减少 case 数量
      // Use the most popular block as the new default, reducing the number of
      // cases.
      assert(MaxPop > 0 && PopSucc);
      Default = PopSucc;

      // 删除所有跳转到新默认块的 case
      Cases.erase(
          llvm::remove_if(
              Cases,
              [PopSucc](const CaseRange &R) { return R.SuccessorBB == PopSucc; }),
          Cases.end());

      // 如果没有剩余的 case，直接跳转到新默认块
      // If there are no cases left, just branch.
      if (Cases.empty()) {
        BranchInst::Create(Default, CurBlock);
        SI->eraseFromParent();
        // 在 PHI 节点中只保留一个OrigBlock入口
        // As all the cases have been replaced with a single branch, only keep
        // one entry in the PHI nodes.
        for (unsigned I = 0; I < (MaxPop - 1); ++I)
          PopSucc->removePredecessor(OrigBlock);
        return;
      }
    } else {
      outs() << "[" << TAG << "] unreachable 处理失败。函数名:\n"
             << F->getName() << ",基本块名:" << CurBlock->getName() <<  '\n';
    }
  }

  // 计算原 switch 中有多少个 case 指向当前默认块
  unsigned NrOfDefaults = (SI->getDefaultDest() == Default) ? 1 : 0;
  for (const auto &Case : SI->cases())
    if (Case.getCaseSuccessor() == Default)
      NrOfDefaults++;

  // 创建新的空默认块以满足if-then结构的控制流需求
  // Create a new, empty default block so that the new hierarchy of
  // if-then statements go to this and the PHI nodes are happy.
  BasicBlock *const NewDefault = BasicBlock::Create(
      SI->getContext(), "NewDefault");
  outs() << "[" << TAG << "] NewDefault:\n" << (*NewDefault) <<  '\n';

  F->insert(Default->getIterator(), NewDefault);
  BranchInst::Create(Default, NewDefault);

  // 使用二分查找的方式将 switch 转换为 if-then 结构
  BasicBlock *const NonSwitchBlock = switchConvert(
      1, "Main",
      Cases.begin(), Cases.end(), LowerBound, UpperBound,
      SwConditionVal,
      OrigBlock, OrigBlock, NewDefault, UnreachableRanges);

  // 更新默认块相关的 PHI 节点信息
  // If there are entries in any PHI nodes for the default edge, make sure
  // to update them as well.
  fixPhis(Default, OrigBlock, NewDefault, NrOfDefaults);

  // 插入跳转指令，指向新生成的 if-then 结构
  // Branch to our shiny new if-then stuff...
//  auto x = OrigBlock->end();
//  outs() << "x=" << (*x) << "\n\n";
  BranchInst::Create(NonSwitchBlock, OrigBlock);

  outs() << "[" << TAG << "] 函数名:\n"
         << F->getName() << ",基本块名:" << CurBlock->getName() << '\n'
         << "NonSwitchBlock:\n" << (*NonSwitchBlock) << "\n\n";

  // 删除原始的 switch 指令
  // We are now done with the switch instruction, delete it.
  BasicBlock *const OldDefault = SI->getDefaultDest();
  CurBlock->erase(SI->getIterator(), ++SI->getIterator());

  // 如果原来的默认块不再有前驱，则将其加入删除列表
  // If the Default block has no more predecessors just add it to DeleteList.
  if (pred_begin(OldDefault) == pred_end(OldDefault))
    DeleteList.insert(OldDefault);
}
