//===-- llvm/Constant.h - Constant class definition -------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the declaration of the Constant class.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_CONSTANT_H
#define LLVM_IR_CONSTANT_H

#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"

namespace llvm {

class ConstantRange;
class APInt;

/// 这是 LLVM 中的一个重要基类，提供了 LLVM 程序中所有常量值的通用功能。
/// 常量是在运行时不可变的值。函数属于常量，因为它们的地址不可变。全局变量同样如此。
///
/// 所有常量都具备此类提供的能力。所有常量都可以有空值，可以拥有操作数列表。
/// 常量可以是简单类型（整型和浮点数值）、复合类型（数组和结构体）、
/// 或基于表达式的（由特定运算符和其他常量值组成的计算结果）。
///
/// 注意：常量是不可变的（一旦创建就永不改变），并且通过结构等价性完全共享。
/// 这意味着两个结构上等价的常量将始终具有相同的地址。常量按需创建且永不删除：
/// 因此客户端无需担心这些对象的生命周期。
///
/// LLVM 常量表示
///
/// This is an important base class in LLVM. It provides the common facilities
/// of all constant values in an LLVM program. A constant is a value that is
/// immutable at runtime. Functions are constants because their address is
/// immutable. Same with global variables.
///
/// All constants share the capabilities provided in this class. All constants
/// can have a null value. They can have an operand list. Constants can be
/// simple (integer and floating point values), complex (arrays and structures),
/// or expression based (computations yielding a constant value composed of
/// only certain operators and other constant values).
///
/// Note that Constants are immutable (once created they never change)
/// and are fully shared by structural equivalence.  This means that two
/// structurally equivalent constants will always have the same address.
/// Constants are created on demand as needed and never deleted: thus clients
/// don't have to worry about the lifetime of the objects.
/// LLVM Constant Representation
class Constant : public User {
protected:
  /**
   * 构造函数
   *
   * @param ty 目标类型
   * @param vty 值类型
   * @param Ops 操作数列表
   * @param NumOps 操作数个数
   */
  Constant(Type *ty, ValueTy vty, Use *Ops, unsigned NumOps)
    : User(ty, vty, Ops, NumOps) {}

  ~Constant() = default;

public:
  void operator=(const Constant &) = delete;
  Constant(const Constant &) = delete;

  /// Return true if this is the value that would be returned by getNullValue.
  bool isNullValue() const;

  /// Returns true if the value is one.
  bool isOneValue() const;

  /// Return true if the value is not the one value, or,
  /// for vectors, does not contain one value elements.
  bool isNotOneValue() const;

  /// Return true if this is the value that would be returned by
  /// getAllOnesValue.
  bool isAllOnesValue() const;

  /// Return true if the value is what would be returned by
  /// getZeroValueForNegation.
  bool isNegativeZeroValue() const;

  /// Return true if the value is negative zero or null value.
  bool isZeroValue() const;

  /// Return true if the value is not the smallest signed value, or,
  /// for vectors, does not contain smallest signed value elements.
  bool isNotMinSignedValue() const;

  /// Return true if the value is the smallest signed value.
  bool isMinSignedValue() const;

  /// Return true if this is a finite and non-zero floating-point scalar
  /// constant or a fixed width vector constant with all finite and non-zero
  /// elements.
  bool isFiniteNonZeroFP() const;

  /// Return true if this is a normal (as opposed to denormal, infinity, nan,
  /// or zero) floating-point scalar constant or a vector constant with all
  /// normal elements. See APFloat::isNormal.
  bool isNormalFP() const;

  /// Return true if this scalar has an exact multiplicative inverse or this
  /// vector has an exact multiplicative inverse for each element in the vector.
  bool hasExactInverseFP() const;

  /// Return true if this is a floating-point NaN constant or a vector
  /// floating-point constant with all NaN elements.
  bool isNaN() const;

  /// Return true if this constant and a constant 'Y' are element-wise equal.
  /// This is identical to just comparing the pointers, with the exception that
  /// for vectors, if only one of the constants has an `undef` element in some
  /// lane, the constants still match.
  bool isElementWiseEqual(Value *Y) const;

  /// Return true if this is a vector constant that includes any undef or
  /// poison elements. Since it is impossible to inspect a scalable vector
  /// element- wise at compile time, this function returns true only if the
  /// entire vector is undef or poison.
  bool containsUndefOrPoisonElement() const;

  /// Return true if this is a vector constant that includes any poison
  /// elements.
  bool containsPoisonElement() const;

  /// Return true if this is a vector constant that includes any strictly undef
  /// (not poison) elements.
  bool containsUndefElement() const;

  /// Return true if this is a fixed width vector constant that includes
  /// any constant expressions.
  bool containsConstantExpression() const;

  /// Return true if the value can vary between threads.
  bool isThreadDependent() const;

  /// Return true if the value is dependent on a dllimport variable.
  bool isDLLImportDependent() const;

  /// Return true if the constant has users other than constant expressions and
  /// other dangling things.
  bool isConstantUsed() const;

  /// This method classifies the entry according to whether or not it may
  /// generate a relocation entry (either static or dynamic). This must be
  /// conservative, so if it might codegen to a relocatable entry, it should say
  /// so.
  ///
  /// FIXME: This really should not be in IR.
  bool needsRelocation() const;
  bool needsDynamicRelocation() const;

  /// For aggregates (struct/array/vector) return the constant that corresponds
  /// to the specified element if possible, or null if not. This can return null
  /// if the element index is a ConstantExpr, if 'this' is a constant expr or
  /// if the constant does not fit into an uint64_t.
  Constant *getAggregateElement(unsigned Elt) const;
  Constant *getAggregateElement(Constant *Elt) const;

  /// 如果向量常量的所有元素都具有相同的值，则返回该值。
  /// 否则，返回 nullptr。通过将 AllowPoison 设置为 true 来忽略有毒元素。
  /// If all elements of the vector constant have the same value, return that
  /// value. Otherwise, return nullptr. Ignore poison elements by setting
  /// AllowPoison to true.
  Constant *getSplatValue(bool AllowPoison = false) const;

  /// If C is a constant integer then return its value, otherwise C must be a
  /// vector of constant integers, all equal, and the common value is returned.
  const APInt &getUniqueInteger() const;

  /// Convert constant to an approximate constant range. For vectors, the
  /// range is the union over the element ranges. Poison elements are ignored.
  ConstantRange toConstantRange() const;

  /// Called if some element of this constant is no longer valid.
  /// At this point only other constants may be on the use_list for this
  /// constant.  Any constants on our Use list must also be destroy'd.  The
  /// implementation must be sure to remove the constant from the list of
  /// available cached constants.  Implementations should implement
  /// destroyConstantImpl to remove constants from any pools/maps they are
  /// contained it.
  void destroyConstant();

  //// Methods for support type inquiry through isa, cast, and dyn_cast:
  static bool classof(const Value *V) {
    static_assert(ConstantFirstVal == 0, "V->getValueID() >= ConstantFirstVal always succeeds");
    return V->getValueID() <= ConstantLastVal;
  }

  /// This method is a special form of User::replaceUsesOfWith
  /// (which does not work on constants) that does work
  /// on constants.  Basically this method goes through the trouble of building
  /// a new constant that is equivalent to the current one, with all uses of
  /// From replaced with uses of To.  After this construction is completed, all
  /// of the users of 'this' are replaced to use the new constant, and then
  /// 'this' is deleted.  In general, you should not call this method, instead,
  /// use Value::replaceAllUsesWith, which automatically dispatches to this
  /// method as needed.
  ///
  void handleOperandChange(Value *, Value *);

  static Constant *getNullValue(Type* Ty);

  /// @returns the value for an integer or vector of integer constant of the
  /// given type that has all its bits set to true.
  /// Get the all ones value
  static Constant *getAllOnesValue(Type* Ty);

  /// Return the value for an integer or pointer constant, or a vector thereof,
  /// with the given scalar value.
  static Constant *getIntegerValue(Type *Ty, const APInt &V);

  /// If there are any dead constant users dangling off of this constant, remove
  /// them. This method is useful for clients that want to check to see if a
  /// global is unused, but don't want to deal with potentially dead constants
  /// hanging off of the globals.
  void removeDeadConstantUsers() const;

  /// Return true if the constant has exactly one live use.
  ///
  /// This returns the same result as calling Value::hasOneUse after
  /// Constant::removeDeadConstantUsers, but doesn't remove dead constants.
  bool hasOneLiveUse() const;

  /// Return true if the constant has no live uses.
  ///
  /// This returns the same result as calling Value::use_empty after
  /// Constant::removeDeadConstantUsers, but doesn't remove dead constants.
  bool hasZeroLiveUses() const;

  const Constant *stripPointerCasts() const {
    return cast<Constant>(Value::stripPointerCasts());
  }

  Constant *stripPointerCasts() {
    return const_cast<Constant*>(
                      static_cast<const Constant *>(this)->stripPointerCasts());
  }

  /// Try to replace undefined constant C or undefined elements in C with
  /// Replacement. If no changes are made, the constant C is returned.
  static Constant *replaceUndefsWith(Constant *C, Constant *Replacement);

  /// Merges undefs of a Constant with another Constant, along with the
  /// undefs already present. Other doesn't have to be the same type as C, but
  /// both must either be scalars or vectors with the same element count. If no
  /// changes are made, the constant C is returned.
  static Constant *mergeUndefsWith(Constant *C, Constant *Other);

  /// Return true if a constant is ConstantData or a ConstantAggregate or
  /// ConstantExpr that contain only ConstantData.
  bool isManifestConstant() const;

private:
  enum PossibleRelocationsTy {
    /// This constant requires no relocations. That is, it holds simple
    /// constants (like integrals).
    NoRelocation = 0,

    /// This constant holds static relocations that can be resolved by the
    /// static linker.
    LocalRelocation = 1,

    /// This constant holds dynamic relocations that the dynamic linker will
    /// need to resolve.
    GlobalRelocation = 2,
  };

  /// Determine what potential relocations may be needed by this constant.
  PossibleRelocationsTy getRelocationInfo() const;

  bool hasNLiveUses(unsigned N) const;
};

} // end namespace llvm

#endif // LLVM_IR_CONSTANT_H
