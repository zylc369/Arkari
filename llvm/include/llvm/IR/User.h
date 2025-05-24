//===- llvm/User.h - User class definition ----------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This class defines the interface that one who uses a Value must implement.
// Each instance of the Value class keeps track of what User's have handles
// to it.
//
//  * Instructions are the largest class of Users.
//  * Constants may be users of other constants (think arrays and stuff)
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_USER_H
#define LLVM_IR_USER_H

#include "llvm/ADT/iterator.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/ErrorHandling.h"
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <iterator>

namespace llvm {

template <typename T> class ArrayRef;
template <typename T> class MutableArrayRef;

/// 用户操作数的编译期定制
///
/// 用于自定义操作数相关的分配器和访问器
///
/// Compile-time customization of User operands.
///
/// Customizes operand-related allocators and accessors.
template <class>
struct OperandTraits;

class User : public Value {
  template <unsigned>
  friend struct HungoffOperandTraits;

  /**
   * 分配内存
   *
   * @param Size 类对象大小
   * @param Us User数组数量
   * @param DescBytes 描述新增字节数
   * @return
   */
  LLVM_ATTRIBUTE_ALWAYS_INLINE static void *
  allocateFixedOperandUser(size_t, unsigned, unsigned);

protected:
  /// 分配一个用户对象，并同时分配其操作数指针。
  ///
  /// 该方法用于需要分配可变数量操作数的子类，即“悬挂式使用”(hung off uses)。
  /// Allocate a User with an operand pointer co-allocated.
  ///
  /// This is used for subclasses which need to allocate a variable number
  /// of operands, ie, 'hung off uses'.
  void *operator new(size_t Size);

  /// 分配一个用户对象，并同时分配其操作数。
  ///
  /// 该方法用于具有固定数量操作数的子类。
  ///
  /// Allocate a User with the operands co-allocated.
  ///
  /// This is used for subclasses which have a fixed number of operands.
  void *operator new(size_t Size, unsigned Us);

  /// 分配一个用户对象并同时分配其操作数。若 DescBytes 非零，
  /// 则会在操作数前额外分配 DescBytes 字节的空间。这些
  /// 字节可通过调用 getDescriptor 访问。
  ///
  /// DescBytes 必须是 sizeof(void *) 的整数倍。所分配的
  /// 描述符（如有）将按 sizeof(void *) 字节对齐。
  ///
  /// 该方法用于具有固定数量操作数的子类。
  ///
  /// Allocate a User with the operands co-allocated.  If DescBytes is non-zero
  /// then allocate an additional DescBytes bytes before the operands. These
  /// bytes can be accessed by calling getDescriptor.
  ///
  /// DescBytes needs to be divisible by sizeof(void *).  The allocated
  /// descriptor, if any, is aligned to sizeof(void *) bytes.
  ///
  /// This is used for subclasses which have a fixed number of operands.
  void *operator new(size_t Size, unsigned Us, unsigned DescBytes);

  User(Type *ty, unsigned vty, Use *, unsigned NumOps)
      : Value(ty, vty) {
    assert(NumOps < (1u << NumUserOperandsBits) && "Too many operands");
    NumUserOperands = NumOps;
    // If we have hung off uses, then the operand list should initially be
    // null.
    assert((!HasHungOffUses || !getOperandList()) &&
           "Error in initializing hung off uses for User");
  }

  /// 分配Use对象数组，随后是一个指向User的指针（其最低位被置位）。
  /// IsPhi用于标识调用者是否为phi节点，这类调用者需要额外分配N个BasicBlock*空间。
  ///
  /// Allocate the array of Uses, followed by a pointer
  /// (with bottom bit set) to the User.
  /// \param IsPhi identifies callers which are phi nodes and which need
  /// N BasicBlock* allocated along with N
  void allocHungoffUses(unsigned N, bool IsPhi = false);

  /// 扩展悬垂式Use的数量。注意：若当前无任何Use，则应调用allocHungoffUses方法。
  /// Grow the number of hung off uses.  Note that allocHungoffUses
  /// should be called if there are no uses.
  void growHungoffUses(unsigned N, bool IsPhi = false);

protected:
  ~User() = default; // Use deleteValue() to delete a generic Instruction.

public:
  User(const User &) = delete;

  /// Free memory allocated for User and Use objects.
  void operator delete(void *Usr);
  /// Placement delete - required by std, called if the ctor throws.
  void operator delete(void *Usr, unsigned) {
    // Note: If a subclass manipulates the information which is required to calculate the
    // Usr memory pointer, e.g. NumUserOperands, the operator delete of that subclass has
    // to restore the changed information to the original value, since the dtor of that class
    // is not called if the ctor fails.
    User::operator delete(Usr);

#ifndef LLVM_ENABLE_EXCEPTIONS
    llvm_unreachable("Constructor throws?");
#endif
  }
  /// Placement delete - required by std, called if the ctor throws.
  void operator delete(void *Usr, unsigned, unsigned) {
    // Note: If a subclass manipulates the information which is required to calculate the
    // Usr memory pointer, e.g. NumUserOperands, the operator delete of that subclass has
    // to restore the changed information to the original value, since the dtor of that class
    // is not called if the ctor fails.
    User::operator delete(Usr);

#ifndef LLVM_ENABLE_EXCEPTIONS
    llvm_unreachable("Constructor throws?");
#endif
  }

protected:
  /**
   * 根据索引 Idx 从 U 类型的对象 that 中获取它的操作数（Use&）。
   *
   * @tparam Idx 索引
   * @tparam U User 或 User 的子类
   * @param that User 或 User 的子类实例
   * @return 返回操作数
   */
  template <int Idx, typename U> static Use &OpFrom(const U *that) {
    // op_end 和 op_begin 调用到了它的父类 VariadicOperandTraits，
    // 实现在 OperandTraits.h 里面

    // 如果 Idx < 0，从 op_end() 开始反向索引（类似 Python 的负索引）。
    // 否则，从 op_begin() 开始正向索引。
    return Idx < 0
      ? OperandTraits<U>::op_end(const_cast<U*>(that))[Idx]
      : OperandTraits<U>::op_begin(const_cast<U*>(that))[Idx];
  }

  /**
   * 根据索引 Idx 获取操作数
   *
   * @tparam Idx 索引
   * @return 返回操作数
   */
  template <int Idx> Use &Op() {
    return OpFrom<Idx>(this);
  }

  /**
   * 根据索引 Idx 获取操作数
   *
   * @tparam Idx 索引
   * @return 返回操作数
   */
  template <int Idx> const Use &Op() const {
    return OpFrom<Idx>(this);
  }

private:
  /**
   * 获得悬挂 User 数组指针
   *
   * @return 返回 User 数组指针
   */
  const Use *getHungOffOperands() const {
    // 返回 const Use*，不允许修改操作数数组指针。const 版本用于只读访问。
    return *(reinterpret_cast<const Use *const *>(this) - 1);
  }

  /**
   * 获得悬挂 User 数组指针
   * 用于动态调整操作数数组（如 setOperandList(Use *NewList)）。
   *
   * @return 返回 User 数组指针
   */
  Use *&getHungOffOperands() {
    /*
     this 原本是 User* 类型，但我们需要访问它前面的 Use*（指针）。
     由于 Use* 本身是一个指针，我们需要：
      1. 将 this 视为 Use**（指向 Use* 的指针）。
        Use** 表示“指向 Use* 的指针”，即 this 现在被认为指向一个 Use*。
      2. -1 回退到前一个 Use* 的位置。
        在指针算术中，ptr - 1 会回退 sizeof(T) 字节（T 是指针类型）。
        在 64 位系统上，Use** 的 -1 会回退 8 字节（Use* 的大小）。
      解引用 *(...) 获取 Use*（操作数数组的指针）。

      示例，假设：
      this 地址是 0x1000（User 对象的起始地址）。
      Use*（操作数数组指针）存储在 0x0FF8（this - 8 字节，64 位系统）。
      代码执行过程：
      Use *&getHungOffOperands() {
        // 1. 将 this (0x1000) 转为 Use**（指向 Use* 的指针）
        Use **ptr = reinterpret_cast<Use **>(this);  // ptr = 0x1000
        // 2. ptr - 1 回退到 0x0FF8（存储 Use* 的位置）
        Use **operandsPtr = ptr - 1;  // 0x1000 - 8 = 0x0FF8
        // 3. 解引用 0x0FF8，获取 Use*（操作数数组指针）
        return *operandsPtr;  // 返回的是 Use*&（指针的引用）
      }
      最终返回的是 0x0FF8 处的 Use*（操作数数组指针）。

      为什么返回 Use *&（指针的引用）？
      返回 Use*&（而不是 Use*）是为了 允许修改 Use* 本身：
      Use *&operands = getHungOffOperands();  // 获取指针的引用
      operands = newUseArray;  // 可以直接修改存储的 Use* 指针
    */
    return *(reinterpret_cast<Use **>(this) - 1);
  }

  /**
   * 获得内嵌 User 数组指针
   *
   * @return 返回 User 数组指针。
   *         这与 User 及其子类的对象创建有关系，详见 allocateFixedOperandUser，
   *         这个函数被 User::operator new 调用
   */
  const Use *getIntrusiveOperands() const {
    return reinterpret_cast<const Use *>(this) - NumUserOperands;
  }

  /**
   * 获得内嵌 User 数组指针
   *
   * @return 返回 User 数组指针。
   *         这与 User 及其子类的对象创建有关系，详见 allocateFixedOperandUser，
   *         这个函数被 User::operator new 调用
   */
  Use *getIntrusiveOperands() {
    return reinterpret_cast<Use *>(this) - NumUserOperands;
  }

  void setOperandList(Use *NewList) {
    assert(HasHungOffUses &&
           "Setting operand list only required for hung off uses");
    getHungOffOperands() = NewList;
  }

public:
  const Use *getOperandList() const {
    return HasHungOffUses ? getHungOffOperands() : getIntrusiveOperands();
  }
  Use *getOperandList() {
    return const_cast<Use *>(static_cast<const User *>(this)->getOperandList());
  }

  Value *getOperand(unsigned i) const {
    assert(i < NumUserOperands && "getOperand() out of range!");
    return getOperandList()[i];
  }

  void setOperand(unsigned i, Value *Val) {
    assert(i < NumUserOperands && "setOperand() out of range!");
    assert((!isa<Constant>((const Value*)this) ||
            isa<GlobalValue>((const Value*)this)) &&
           "Cannot mutate a constant with setOperand!");
    getOperandList()[i] = Val;
  }

  const Use &getOperandUse(unsigned i) const {
    assert(i < NumUserOperands && "getOperandUse() out of range!");
    return getOperandList()[i];
  }
  Use &getOperandUse(unsigned i) {
    assert(i < NumUserOperands && "getOperandUse() out of range!");
    return getOperandList()[i];
  }

  unsigned getNumOperands() const { return NumUserOperands; }

  /// Returns the descriptor co-allocated with this User instance.
  ArrayRef<const uint8_t> getDescriptor() const;

  /// Returns the descriptor co-allocated with this User instance.
  MutableArrayRef<uint8_t> getDescriptor();

  /// Set the number of operands on a GlobalVariable.
  ///
  /// GlobalVariable always allocates space for a single operands, but
  /// doesn't always use it.
  ///
  /// FIXME: As that the number of operands is used to find the start of
  /// the allocated memory in operator delete, we need to always think we have
  /// 1 operand before delete.
  void setGlobalVariableNumOperands(unsigned NumOps) {
    assert(NumOps <= 1 && "GlobalVariable can only have 0 or 1 operands");
    NumUserOperands = NumOps;
  }

  /// Subclasses with hung off uses need to manage the operand count
  /// themselves.  In these instances, the operand count isn't used to find the
  /// OperandList, so there's no issue in having the operand count change.
  void setNumHungOffUseOperands(unsigned NumOps) {
    assert(HasHungOffUses && "Must have hung off uses to use this method");
    assert(NumOps < (1u << NumUserOperandsBits) && "Too many operands");
    NumUserOperands = NumOps;
  }

  /// A droppable user is a user for which uses can be dropped without affecting
  /// correctness and should be dropped rather than preventing a transformation
  /// from happening.
  bool isDroppable() const;

  // ---------------------------------------------------------------------------
  // Operand Iterator interface...
  //
  using op_iterator = Use*;
  using const_op_iterator = const Use*;
  using op_range = iterator_range<op_iterator>;
  using const_op_range = iterator_range<const_op_iterator>;

  op_iterator       op_begin()       { return getOperandList(); }
  const_op_iterator op_begin() const { return getOperandList(); }
  op_iterator       op_end()         {
    return getOperandList() + NumUserOperands;
  }
  const_op_iterator op_end()   const {
    return getOperandList() + NumUserOperands;
  }
  op_range operands() {
    return op_range(op_begin(), op_end());
  }
  const_op_range operands() const {
    return const_op_range(op_begin(), op_end());
  }

  /// Iterator for directly iterating over the operand Values.
  struct value_op_iterator
      : iterator_adaptor_base<value_op_iterator, op_iterator,
                              std::random_access_iterator_tag, Value *,
                              ptrdiff_t, Value *, Value *> {
    explicit value_op_iterator(Use *U = nullptr) : iterator_adaptor_base(U) {}

    Value *operator*() const { return *I; }
    Value *operator->() const { return operator*(); }
  };

  value_op_iterator value_op_begin() {
    return value_op_iterator(op_begin());
  }
  value_op_iterator value_op_end() {
    return value_op_iterator(op_end());
  }
  iterator_range<value_op_iterator> operand_values() {
    return make_range(value_op_begin(), value_op_end());
  }

  struct const_value_op_iterator
      : iterator_adaptor_base<const_value_op_iterator, const_op_iterator,
                              std::random_access_iterator_tag, const Value *,
                              ptrdiff_t, const Value *, const Value *> {
    explicit const_value_op_iterator(const Use *U = nullptr) :
      iterator_adaptor_base(U) {}

    const Value *operator*() const { return *I; }
    const Value *operator->() const { return operator*(); }
  };

  const_value_op_iterator value_op_begin() const {
    return const_value_op_iterator(op_begin());
  }
  const_value_op_iterator value_op_end() const {
    return const_value_op_iterator(op_end());
  }
  iterator_range<const_value_op_iterator> operand_values() const {
    return make_range(value_op_begin(), value_op_end());
  }

  /// Drop all references to operands.
  ///
  /// This function is in charge of "letting go" of all objects that this User
  /// refers to.  This allows one to 'delete' a whole class at a time, even
  /// though there may be circular references...  First all references are
  /// dropped, and all use counts go to zero.  Then everything is deleted for
  /// real.  Note that no operations are valid on an object that has "dropped
  /// all references", except operator delete.
  void dropAllReferences() {
    for (Use &U : operands())
      U.set(nullptr);
  }

  /// Replace uses of one Value with another.
  ///
  /// Replaces all references to the "From" definition with references to the
  /// "To" definition. Returns whether any uses were replaced.
  bool replaceUsesOfWith(Value *From, Value *To);

  // Methods for support type inquiry through isa, cast, and dyn_cast:
  static bool classof(const Value *V) {
    return isa<Instruction>(V) || isa<Constant>(V);
  }
};

// Either Use objects, or a Use pointer can be prepended to User.
static_assert(alignof(Use) >= alignof(User),
              "Alignment is insufficient after objects prepended to User");
static_assert(alignof(Use *) >= alignof(User),
              "Alignment is insufficient after objects prepended to User");

template<> struct simplify_type<User::op_iterator> {
  using SimpleType = Value*;

  static SimpleType getSimplifiedValue(User::op_iterator &Val) {
    return Val->get();
  }
};
template<> struct simplify_type<User::const_op_iterator> {
  using SimpleType = /*const*/ Value*;

  static SimpleType getSimplifiedValue(User::const_op_iterator &Val) {
    return Val->get();
  }
};

} // end namespace llvm

#endif // LLVM_IR_USER_H
