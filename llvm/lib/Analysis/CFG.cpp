//===-- CFG.cpp - BasicBlock analysis --------------------------------------==//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This family of functions performs analyses on basic blocks, and instructions
// contained within basic blocks.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

// The max number of basic blocks explored during reachability analysis between
// two basic blocks. This is kept reasonably small to limit compile time when
// repeatedly used by clients of this analysis (such as captureTracking).
static cl::opt<unsigned> DefaultMaxBBsToExplore(
    "dom-tree-reachability-max-bbs-to-explore", cl::Hidden,
    cl::desc("Max number of BBs to explore for reachability analysis"),
    cl::init(32));

/// FindFunctionBackedges - Analyze the specified function to find all of the
/// loop backedges in the function and return them.  This is a relatively cheap
/// (compared to computing dominators and loop info) analysis.
///
/// The output is added to Result, as pairs of <from,to> edge info.
void llvm::FindFunctionBackedges(const Function &F,
     SmallVectorImpl<std::pair<const BasicBlock*,const BasicBlock*> > &Result) {
  const BasicBlock *BB = &F.getEntryBlock();
  if (succ_empty(BB))
    return;

  SmallPtrSet<const BasicBlock*, 8> Visited;
  SmallVector<std::pair<const BasicBlock *, const_succ_iterator>, 8> VisitStack;
  SmallPtrSet<const BasicBlock*, 8> InStack;

  Visited.insert(BB);
  VisitStack.push_back(std::make_pair(BB, succ_begin(BB)));
  InStack.insert(BB);
  do {
    std::pair<const BasicBlock *, const_succ_iterator> &Top = VisitStack.back();
    const BasicBlock *ParentBB = Top.first;
    const_succ_iterator &I = Top.second;

    bool FoundNew = false;
    while (I != succ_end(ParentBB)) {
      BB = *I++;
      if (Visited.insert(BB).second) {
        FoundNew = true;
        break;
      }
      // Successor is in VisitStack, it's a back edge.
      if (InStack.count(BB))
        Result.push_back(std::make_pair(ParentBB, BB));
    }

    if (FoundNew) {
      // Go down one level if there is a unvisited successor.
      InStack.insert(BB);
      VisitStack.push_back(std::make_pair(BB, succ_begin(BB)));
    } else {
      // Go up one level.
      InStack.erase(VisitStack.pop_back_val().first);
    }
  } while (!VisitStack.empty());
}

/// GetSuccessorNumber - Search for the specified successor of basic block BB
/// and return its position in the terminator instruction's list of
/// successors.  It is an error to call this with a block that is not a
/// successor.
unsigned llvm::GetSuccessorNumber(const BasicBlock *BB,
    const BasicBlock *Succ) {
  const Instruction *Term = BB->getTerminator();
#ifndef NDEBUG
  unsigned e = Term->getNumSuccessors();
#endif
  for (unsigned i = 0; ; ++i) {
    assert(i != e && "Didn't find edge?");
    if (Term->getSuccessor(i) == Succ)
      return i;
  }
}

/// isCriticalEdge - 如果指定边是关键边，则返回 true。关键边是指从具有多个后继的区块到具有多个前继的区块的边。
/// isCriticalEdge - Return true if the specified edge is a critical edge.
/// Critical edges are edges from a block with multiple successors to a block
/// with multiple predecessors.
bool llvm::isCriticalEdge(const Instruction *TI, unsigned SuccNum,
                          bool AllowIdenticalEdges) {
  assert(SuccNum < TI->getNumSuccessors() && "Illegal edge specification!");
  return isCriticalEdge(TI, TI->getSuccessor(SuccNum), AllowIdenticalEdges);
}

bool llvm::isCriticalEdge(const Instruction *TI, const BasicBlock *Dest,
                          bool AllowIdenticalEdges) {
  assert(TI->isTerminator() && "Must be a terminator to have successors!");

  // 如果 TI 所在的基本块只有一个后继（即只有一条出口边），直接返回 false，因为关键边要求源块有多个后继。
  if (TI->getNumSuccessors() == 1) return false;

  // 确保 TI 所在的基本块确实是 Dest 的前驱之一。
  assert(is_contained(predecessors(Dest), TI->getParent()) &&
         "No edge between TI's block and Dest.");

  // 前驱迭代与分析，获取前驱起始和结束迭代器
  const_pred_iterator I = pred_begin(Dest), E = pred_end(Dest);

  // 如果有多个前任，这就是关键边……
  // If there is more than one predecessor, this is a critical edge...
  assert(I != E && "No preds, but we have an edge to the block?");
  const BasicBlock *FirstPred = *I;
  // 跳过一条边（即 TI 所在块到 Dest 的边）
  ++I;        // Skip one edge due to the incoming arc from TI.
  if (!AllowIdenticalEdges) {
    // 当 AllowIdenticalEdges = false 时，只要 Dest 有其他前驱块（即使来自同一源块），返回 true（关键边）。
    return I != E;
  }

  // 如果 AllowIdenticalEdges 为 true，
  // 那么当且仅当所有前驱（predecessors）都来自终止指令（TI）所在的基本块时，
  // 我们允许将该边视为非关键边（non-critical）。
  // If AllowIdenticalEdges is true, then we allow this edge to be considered
  // non-critical iff all preds come from TI's block.
  // 当 AllowIdenticalEdges = true 时，只有所有前驱块都来自 TI 所在块，才返回 false（非关键边）。
  for (; I != E; ++I)
    if (*I != FirstPred)
      return true;
  return false;
}

// LoopInfo contains a mapping from basic block to the innermost loop. Find
// the outermost loop in the loop nest that contains BB.
static const Loop *getOutermostLoop(const LoopInfo *LI, const BasicBlock *BB) {
  const Loop *L = LI->getLoopFor(BB);
  return L ? L->getOutermostLoop() : nullptr;
}

template <class StopSetT>
static bool isReachableImpl(SmallVectorImpl<BasicBlock *> &Worklist,
                            const StopSetT &StopSet,
                            const SmallPtrSetImpl<BasicBlock *> *ExclusionSet,
                            const DominatorTree *DT, const LoopInfo *LI) {
  // When a stop block is unreachable, it's dominated from everywhere,
  // regardless of whether there's a path between the two blocks.
  if (DT) {
    for (auto *BB : StopSet) {
      if (!DT->isReachableFromEntry(BB)) {
        DT = nullptr;
        break;
      }
    }
  }

  // We can't skip directly from a block that dominates the stop block if the
  // exclusion block is potentially in between.
  if (ExclusionSet && !ExclusionSet->empty())
    DT = nullptr;

  // Normally any block in a loop is reachable from any other block in a loop,
  // however excluded blocks might partition the body of a loop to make that
  // untrue.
  SmallPtrSet<const Loop *, 8> LoopsWithHoles;
  if (LI && ExclusionSet) {
    for (auto *BB : *ExclusionSet) {
      if (const Loop *L = getOutermostLoop(LI, BB))
        LoopsWithHoles.insert(L);
    }
  }

  SmallPtrSet<const Loop *, 2> StopLoops;
  if (LI) {
    for (auto *StopSetBB : StopSet) {
      if (const Loop *L = getOutermostLoop(LI, StopSetBB))
        StopLoops.insert(L);
    }
  }

  unsigned Limit = DefaultMaxBBsToExplore;
  SmallPtrSet<const BasicBlock*, 32> Visited;
  do {
    BasicBlock *BB = Worklist.pop_back_val();
    if (!Visited.insert(BB).second)
      continue;
    if (StopSet.contains(BB))
      return true;
    if (ExclusionSet && ExclusionSet->count(BB))
      continue;
    if (DT) {
      if (llvm::any_of(StopSet, [&](const BasicBlock *StopBB) {
            return DT->dominates(BB, StopBB);
          }))
        return true;
    }

    const Loop *Outer = nullptr;
    if (LI) {
      Outer = getOutermostLoop(LI, BB);
      // If we're in a loop with a hole, not all blocks in the loop are
      // reachable from all other blocks. That implies we can't simply jump to
      // the loop's exit blocks, as that exit might need to pass through an
      // excluded block. Clear Outer so we process BB's successors.
      if (LoopsWithHoles.count(Outer))
        Outer = nullptr;
      if (StopLoops.contains(Outer))
        return true;
    }

    if (!--Limit) {
      // We haven't been able to prove it one way or the other. Conservatively
      // answer true -- that there is potentially a path.
      return true;
    }

    if (Outer) {
      // All blocks in a single loop are reachable from all other blocks. From
      // any of these blocks, we can skip directly to the exits of the loop,
      // ignoring any other blocks inside the loop body.
      Outer->getExitBlocks(Worklist);
    } else {
      Worklist.append(succ_begin(BB), succ_end(BB));
    }
  } while (!Worklist.empty());

  // We have exhausted all possible paths and are certain that 'To' can not be
  // reached from 'From'.
  return false;
}

template <class T> class SingleEntrySet {
public:
  using const_iterator = const T *;

  SingleEntrySet(T Elem) : Elem(Elem) {}

  bool contains(T Other) const { return Elem == Other; }

  const_iterator begin() const { return &Elem; }
  const_iterator end() const { return &Elem + 1; }

private:
  T Elem;
};

bool llvm::isPotentiallyReachableFromMany(
    SmallVectorImpl<BasicBlock *> &Worklist, const BasicBlock *StopBB,
    const SmallPtrSetImpl<BasicBlock *> *ExclusionSet, const DominatorTree *DT,
    const LoopInfo *LI) {
  return isReachableImpl<SingleEntrySet<const BasicBlock *>>(
      Worklist, SingleEntrySet<const BasicBlock *>(StopBB), ExclusionSet, DT,
      LI);
}

bool llvm::isManyPotentiallyReachableFromMany(
    SmallVectorImpl<BasicBlock *> &Worklist,
    const SmallPtrSetImpl<const BasicBlock *> &StopSet,
    const SmallPtrSetImpl<BasicBlock *> *ExclusionSet, const DominatorTree *DT,
    const LoopInfo *LI) {
  return isReachableImpl<SmallPtrSetImpl<const BasicBlock *>>(
      Worklist, StopSet, ExclusionSet, DT, LI);
}

bool llvm::isPotentiallyReachable(
    const BasicBlock *A, const BasicBlock *B,
    const SmallPtrSetImpl<BasicBlock *> *ExclusionSet, const DominatorTree *DT,
    const LoopInfo *LI) {
  assert(A->getParent() == B->getParent() &&
         "This analysis is function-local!");

  if (DT) {
    if (DT->isReachableFromEntry(A) && !DT->isReachableFromEntry(B))
      return false;
    if (!ExclusionSet || ExclusionSet->empty()) {
      if (A->isEntryBlock() && DT->isReachableFromEntry(B))
        return true;
      if (B->isEntryBlock() && DT->isReachableFromEntry(A))
        return false;
    }
  }

  SmallVector<BasicBlock*, 32> Worklist;
  Worklist.push_back(const_cast<BasicBlock*>(A));

  return isPotentiallyReachableFromMany(Worklist, B, ExclusionSet, DT, LI);
}

bool llvm::isPotentiallyReachable(
    const Instruction *A, const Instruction *B,
    const SmallPtrSetImpl<BasicBlock *> *ExclusionSet, const DominatorTree *DT,
    const LoopInfo *LI) {
  assert(A->getParent()->getParent() == B->getParent()->getParent() &&
         "This analysis is function-local!");

  if (A->getParent() == B->getParent()) {
    // The same block case is special because it's the only time we're looking
    // within a single block to see which instruction comes first. Once we
    // start looking at multiple blocks, the first instruction of the block is
    // reachable, so we only need to determine reachability between whole
    // blocks.
    BasicBlock *BB = const_cast<BasicBlock *>(A->getParent());

    // If the block is in a loop then we can reach any instruction in the block
    // from any other instruction in the block by going around a backedge.
    if (LI && LI->getLoopFor(BB) != nullptr)
      return true;

    // If A comes before B, then B is definitively reachable from A.
    if (A == B || A->comesBefore(B))
      return true;

    // Can't be in a loop if it's the entry block -- the entry block may not
    // have predecessors.
    if (BB->isEntryBlock())
      return false;

    // Otherwise, continue doing the normal per-BB CFG walk.
    SmallVector<BasicBlock*, 32> Worklist;
    Worklist.append(succ_begin(BB), succ_end(BB));
    if (Worklist.empty()) {
      // We've proven that there's no path!
      return false;
    }

    return isPotentiallyReachableFromMany(Worklist, B->getParent(),
                                          ExclusionSet, DT, LI);
  }

  return isPotentiallyReachable(
      A->getParent(), B->getParent(), ExclusionSet, DT, LI);
}
