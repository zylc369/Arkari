//===- DemoteRegToStack.cpp - Move a virtual register to the stack --------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
using namespace llvm;


/// DemoteRegToStack - 该函数接收一条指令计算得到的虚拟寄存器，并将其替换为通过alloca分配的栈帧槽位。
/// 这样可以在修改控制流图时无需担心破坏该值的SSA信息。
/// 函数返回为指令I创建栈槽所插入的alloca指针。
///
/// DemoteRegToStack - This function takes a virtual register computed by an
/// Instruction and replaces it with a slot in the stack frame, allocated via
/// alloca.  This allows the CFG to be changed around without fear of
/// invalidating the SSA information for the value.  It returns the pointer to
/// the alloca inserted to create a stack slot for I.
AllocaInst *llvm::DemoteRegToStack(Instruction &I, bool VolatileLoads,
                                   std::optional<BasicBlock::iterator> AllocaPoint) {
  // 如果指令没有使用者，直接删除并返回空指针
  if (I.use_empty()) {
    I.eraseFromParent();
    return nullptr;
  }

  Function *F = I.getParent()->getParent();
  const DataLayout &DL = F->getDataLayout();

  // 创建栈槽来保存值
  // Create a stack slot to hold the value.
  AllocaInst *Slot;
  if (AllocaPoint) {
    Slot = new AllocaInst(I.getType(), DL.getAllocaAddrSpace(), nullptr,
                          I.getName()+".reg2mem", *AllocaPoint);
  } else {
    Slot = new AllocaInst(I.getType(), DL.getAllocaAddrSpace(), nullptr,
                          I.getName() + ".reg2mem", F->getEntryBlock().begin());
  }

  // 如果被调用指令（invoke）的正常边是关键边，则不能直接降级到栈
  // 需要分割关键边并创建基本块来插入存储指令
  //
  // We cannot demote invoke instructions to the stack if their normal edge
  // is critical. Therefore, split the critical edge and create a basic block
  // into which the store can be inserted.
  if (InvokeInst *II = dyn_cast<InvokeInst>(&I)) {
    if (!II->getNormalDest()->getSinglePredecessor()) {
      unsigned SuccNum = GetSuccessorNumber(II->getParent(), II->getNormalDest());
      assert(isCriticalEdge(II, SuccNum) && "Expected a critical edge!");
      BasicBlock *BB = SplitCriticalEdge(II, SuccNum);
      assert(BB && "Unable to split critical edge.");
      (void)BB;
    }
  } else if (CallBrInst *CBI = dyn_cast<CallBrInst>(&I)) {
    for (unsigned i = 0; i < CBI->getNumSuccessors(); i++) {
      auto *Succ = CBI->getSuccessor(i);
      if (!Succ->getSinglePredecessor()) {
        assert(isCriticalEdge(II, i) && "Expected a critical edge!");
        [[maybe_unused]] BasicBlock *BB = SplitCriticalEdge(II, i);
        assert(BB && "Unable to split critical edge.");
      }
    }
  }

  // 将所有使用该指令的地方改为从栈槽读取
  // Change all of the users of the instruction to read from the stack slot.
  while (!I.use_empty()) {
    Instruction *U = cast<Instruction>(I.user_back());
    if (PHINode *PN = dyn_cast<PHINode>(U)) {
      // 若当前为PHI节点，则不能在use指令前直接插入值的加载操作。
      // 此时应在对应前驱基本块中插入该输入值的加载指令。
      //
      // 注意：若存在同一基本块到该PHI节点的多条边，则不能生成多次加载。
      // 问题在于这将导致PHI节点从同一基本块接收多个加载结果值，
      // 这违反了SSA形式的规范。为此，我们通过记录并复用已插入的加载指令来避免该问题。
      //
      // If this is a PHI node, we can't insert a load of the value before the
      // use.  Instead insert the load in the predecessor block corresponding
      // to the incoming value.
      //
      // Note that if there are multiple edges from a basic block to this PHI
      // node that we cannot have multiple loads. The problem is that the
      // resulting PHI node will have multiple values (from each load) coming in
      // from the same block, which is illegal SSA form. For this reason, we
      // keep track of and reuse loads we insert.
      DenseMap<BasicBlock*, Value*> Loads;
      for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i)
        if (PN->getIncomingValue(i) == &I) {
          Value *&V = Loads[PN->getIncomingBlock(i)];
          if (!V) {
            // 在前驱块中插入加载指令
            // Insert the load into the predecessor block
            V = new LoadInst(I.getType(), Slot, I.getName() + ".reload",
                             VolatileLoads,
                             PN->getIncomingBlock(i)->getTerminator()->getIterator());
            Loads[PN->getIncomingBlock(i)] = V;
          }
          PN->setIncomingValue(i, V);
        }

    } else {
      // 普通指令直接插入加载
      // If this is a normal instruction, just insert a load.
      Value *V = new LoadInst(I.getType(), Slot, I.getName() + ".reload",
                              VolatileLoads, U->getIterator());
      U->replaceUsesOfWith(&I, V);
    }
  }

  // 将计算得到的值存入栈槽。需要特别注意：当I是invoke指令时，
  // 不能在终止指令之后插入存储操作。
  //
  // Insert stores of the computed value into the stack slot. We have to be
  // careful if I is an invoke instruction, because we can't insert the store
  // AFTER the terminator instruction.
  BasicBlock::iterator InsertPt;
  if (!I.isTerminator()) {
    InsertPt = ++I.getIterator();
    // 不要插入到PHI节点或landingpad指令之前
    // Don't insert before PHI nodes or landingpad instrs.
    for (; isa<PHINode>(InsertPt) || InsertPt->isEHPad(); ++InsertPt)
      if (isa<CatchSwitchInst>(InsertPt))
        break;
    if (isa<CatchSwitchInst>(InsertPt)) {
      for (BasicBlock *Handler : successors(&*InsertPt))
        new StoreInst(&I, Slot, Handler->getFirstInsertionPt());
      return Slot;
    }
  } else if (InvokeInst *II = dyn_cast<InvokeInst>(&I)) {
    InsertPt = II->getNormalDest()->getFirstInsertionPt();
  } else if (CallBrInst *CBI = dyn_cast<CallBrInst>(&I)) {
    for (BasicBlock *Succ : successors(CBI))
      new StoreInst(CBI, Slot, Succ->getFirstInsertionPt());
    return Slot;
  } else {
    llvm_unreachable("Unsupported terminator for Reg2Mem");
  }

  new StoreInst(&I, Slot, InsertPt);
  return Slot;
}

/// DemotePHIToStack - 该函数接收一个PHI节点计算得到的虚拟寄存器，并将其替换为通过alloca分配的栈帧槽位。
/// PHI节点将被删除。函数返回所插入的alloca指针。
///
/// DemotePHIToStack - This function takes a virtual register computed by a PHI
/// node and replaces it with a slot in the stack frame allocated via alloca.
/// The PHI node is deleted. It returns the pointer to the alloca inserted.
AllocaInst *llvm::DemotePHIToStack(PHINode *P, std::optional<BasicBlock::iterator> AllocaPoint) {
  if (P->use_empty()) {
    P->eraseFromParent();
    return nullptr;
  }

  const DataLayout &DL = P->getDataLayout();

  // Create a stack slot to hold the value.
  AllocaInst *Slot;
  if (AllocaPoint) {
    Slot = new AllocaInst(P->getType(), DL.getAllocaAddrSpace(), nullptr,
                          P->getName()+".reg2mem", *AllocaPoint);
  } else {
    Function *F = P->getParent()->getParent();
    Slot = new AllocaInst(P->getType(), DL.getAllocaAddrSpace(), nullptr,
                          P->getName() + ".reg2mem",
                          F->getEntryBlock().begin());
  }

  // Iterate over each operand inserting a store in each predecessor.
  for (unsigned i = 0, e = P->getNumIncomingValues(); i < e; ++i) {
    if (InvokeInst *II = dyn_cast<InvokeInst>(P->getIncomingValue(i))) {
      assert(II->getParent() != P->getIncomingBlock(i) &&
             "Invoke edge not supported yet"); (void)II;
    }
    new StoreInst(P->getIncomingValue(i), Slot,
                  P->getIncomingBlock(i)->getTerminator()->getIterator());
  }

  // Insert a load in place of the PHI and replace all uses.
  BasicBlock::iterator InsertPt = P->getIterator();
  // Don't insert before PHI nodes or landingpad instrs.
  for (; isa<PHINode>(InsertPt) || InsertPt->isEHPad(); ++InsertPt)
    if (isa<CatchSwitchInst>(InsertPt))
      break;
  if (isa<CatchSwitchInst>(InsertPt)) {
    // We need a separate load before each actual use of the PHI
    SmallVector<Instruction *, 4> Users;
    for (User *U : P->users()) {
      Instruction *User = cast<Instruction>(U);
      Users.push_back(User);
    }
    for (Instruction *User : Users) {
      Value *V =
          new LoadInst(P->getType(), Slot, P->getName() + ".reload", User->getIterator());
      User->replaceUsesOfWith(P, V);
    }
  } else {
    Value *V =
        new LoadInst(P->getType(), Slot, P->getName() + ".reload", InsertPt);
    P->replaceAllUsesWith(V);
  }
  // Delete PHI.
  P->eraseFromParent();
  return Slot;
}
