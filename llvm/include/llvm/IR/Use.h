//===- llvm/Use.h - Definition of the Use class -----------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
///
/// This defines the Use class.  The Use class represents the operand of an
/// instruction or some other User instance which refers to a Value.  The Use
/// class keeps the "use list" of the referenced value up to date.
///
/// Pointer tagging is used to efficiently find the User corresponding to a Use
/// without having to store a User pointer in every Use. A User is preceded in
/// memory by all the Uses corresponding to its operands, and the low bits of
/// one of the fields (Prev) of the Use class are used to encode offsets to be
/// able to find that User given a pointer to any Use. For details, see:
///
///   http://www.llvm.org/docs/ProgrammersManual.html#UserLayout
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_USE_H
#define LLVM_IR_USE_H

#include "llvm-c/Types.h"
#include "llvm/Support/CBindingWrapping.h"
#include "llvm/Support/Compiler.h"

namespace llvm {

template <typename> struct simplify_type;
class User;
class Value;

/// Use 表示 Value 定义与其 users 之间的边。
/// 理论上，这是一个二维链表。它支持遍历特定值定义的所有用途。
/// 它还支持从 User 的操作数跳转到已使用的值，以及当我们从 Value 的 User 到达时直接跳转到 uses。
///
/// A Use represents the edge between a Value definition and its users.
///
/// This is notionally a two-dimensional linked list. It supports traversing
/// all of the uses for a particular value definition. It also supports jumping
/// directly to the used value when we arrive from the User's operands, and
/// jumping directly to the User when we arrive from the Value's uses.
class Use {
public:
  Use(const Use &U) = delete;

  /// Provide a fast substitute to std::swap<Use>
  /// that also works with less standard-compliant compilers
  void swap(Use &RHS);

private:
  /// Destructor - Only for zap()
  ~Use() {
    if (Val)
      removeFromList();
  }

  /// Constructor
  Use(User *Parent) : Parent(Parent) {}

public:
  friend class Value;
  friend class User;

  operator Value *() const { return Val; }
  Value *get() const { return Val; }

  /// 返回包含此用途的用户。（返回包含此 Use 的 User。）
  ///
  /// 例如，对于指令操作数，这将返回指令。
  ///
  /// Returns the User that contains this Use.
  ///
  /// For an instruction operand, for example, this will return the
  /// instruction.
  User *getUser() const { return Parent; };

  inline void set(Value *Val);

  /// 在 Value.h 里面实现
  inline Value *operator=(Value *RHS);
  inline const Use &operator=(const Use &RHS);

  Value *operator->() { return Val; }
  const Value *operator->() const { return Val; }

  Use *getNext() const { return Next; }

  // 返回此用途在其用户中的操作数#。
  /// Return the operand # of this use in its User.
  unsigned getOperandNo() const;

  /// 当用户的操作数数量发生变化时，销毁使用的操作数。
  /// Destroys Use operands when the number of operands of
  /// a User changes.
  static void zap(Use *Start, const Use *Stop, bool del = false);

private:

  /// 指向被使用的值(Value)的指针
  Value *Val = nullptr;
  Use *Next = nullptr;
  Use **Prev = nullptr;
  User *Parent = nullptr;

  /**
   * 将当前 Use 对象添加到由 List 参数指定的 User 指针链表的头部。
   *
   * @param List 链表
   */
  void addToList(Use **List) {
    // 将当前 Use 对象的 Next 指针赋值为入参链表第一个元素的地址
    Next = *List;
    if (Next) {
      // 更新Next节点的Prev指针，让它指向Next的指针
      Next->Prev = &Next;
    }
    // 置本Prev指针指向链表头指针
    Prev = List;
    // 让链表头指针指向本节点(完成头部插入)
    *Prev = this;
  }

  /**
   * 将当前 User 对象从链表删除
   */
  void removeFromList() {
    *Prev = Next;
    if (Next) {
      // 后继节点存在，让后继节点的 Prev 指向前驱节点
      Next->Prev = Prev;
    }
  }
};

/// Allow clients to treat uses just like values when using
/// casting operators.
template <> struct simplify_type<Use> {
  using SimpleType = Value *;

  static SimpleType getSimplifiedValue(Use &Val) { return Val.get(); }
};
template <> struct simplify_type<const Use> {
  using SimpleType = /*const*/ Value *;

  static SimpleType getSimplifiedValue(const Use &Val) { return Val.get(); }
};

// Create wrappers for C Binding types (see CBindingWrapping.h).
DEFINE_SIMPLE_CONVERSION_FUNCTIONS(Use, LLVMUseRef)

} // end namespace llvm

#endif // LLVM_IR_USE_H
