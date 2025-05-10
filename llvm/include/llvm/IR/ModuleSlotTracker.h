//===-- llvm/IR/ModuleSlotTracker.h -----------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_MODULESLOTTRACKER_H
#define LLVM_IR_MODULESLOTTRACKER_H

#include <functional>
#include <memory>
#include <utility>
#include <vector>

namespace llvm {

class Module;
class Function;
class SlotTracker;
class Value;
class MDNode;

/// Abstract interface of slot tracker storage.
class AbstractSlotTrackerStorage {
public:
  virtual ~AbstractSlotTrackerStorage();

  virtual unsigned getNextMetadataSlot() = 0;

  virtual void createMetadataSlot(const MDNode *) = 0;
  virtual int getMetadataSlot(const MDNode *) = 0;
};

/// 管理用于打印IR的SlotTracker生命周期。
/// 作为AsmWriter内部使用的SlotTracker的封装类。
/// 优化机制：允许调用方共享模块或函数中元数据的初始化成本（避免重复计算）。
/// IR变更风险：如果底层IR在ModuleSlotTracker使用期间被修改，可能导致：
///     输出<badref>等错误标记。<badref>：当IR被修改后，引用失效的占位符（类似悬垂指针的文本表示）。
///     更严重的情况：打印完全错误的槽位编号（如%1错误指向其他值）。
///
/// Manage lifetime of a slot tracker for printing IR.
///
/// Wrapper around the \a SlotTracker used internally by \a AsmWriter.  This
/// class allows callers to share the cost of incorporating the metadata in a
/// module or a function.
///
/// If the IR changes from underneath \a ModuleSlotTracker, strings like
/// "<badref>" will be printed, or, worse, the wrong slots entirely.
class ModuleSlotTracker {
  /// 插槽追踪器的存储。
  /// Storage for a slot tracker.
  std::unique_ptr<SlotTracker> MachineStorage;
  bool ShouldCreateStorage = false;
  bool ShouldInitializeAllMetadata = false;

  const Module *M = nullptr;
  const Function *F = nullptr;
  SlotTracker *Machine = nullptr;

  std::function<void(AbstractSlotTrackerStorage *, const Module *, bool)>
      ProcessModuleHookFn;
  std::function<void(AbstractSlotTrackerStorage *, const Function *, bool)>
      ProcessFunctionHookFn;

public:
  /// Wrap a preinitialized SlotTracker.
  ModuleSlotTracker(SlotTracker &Machine, const Module *M,
                    const Function *F = nullptr);

  /// Construct a slot tracker from a module.
  ///
  /// If \a M is \c nullptr, uses a null slot tracker.  Otherwise, initializes
  /// a slot tracker, and initializes all metadata slots.  \c
  /// ShouldInitializeAllMetadata defaults to true because this is expected to
  /// be shared between multiple callers, and otherwise MDNode references will
  /// not match up.
  explicit ModuleSlotTracker(const Module *M,
                             bool ShouldInitializeAllMetadata = true);

  /// Destructor to clean up storage.
  virtual ~ModuleSlotTracker();

  /// Lazily creates a slot tracker.
  SlotTracker *getMachine();

  const Module *getModule() const { return M; }
  const Function *getCurrentFunction() const { return F; }

  /// 合并给定的函数。
  /// 清除当前合并的功能并合并 F。如果 F 当前已合并，则这是一个无操作。
  ///
  /// Incorporate the given function.
  ///
  /// Purge the currently incorporated function and incorporate \c F.  If \c F
  /// is currently incorporated, this is a no-op.
  void incorporateFunction(const Function &F);

  /// Return the slot number of the specified local value.
  ///
  /// A function that defines this value should be incorporated prior to calling
  /// this method.
  /// Return -1 if the value is not in the function's SlotTracker.
  int getLocalSlot(const Value *V);

  void setProcessHook(
      std::function<void(AbstractSlotTrackerStorage *, const Module *, bool)>);
  void setProcessHook(std::function<void(AbstractSlotTrackerStorage *,
                                         const Function *, bool)>);

  using MachineMDNodeListType =
      std::vector<std::pair<unsigned, const MDNode *>>;

  void collectMDNodes(MachineMDNodeListType &L, unsigned LB, unsigned UB) const;
};

} // end namespace llvm

#endif
