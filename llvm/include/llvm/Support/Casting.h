//===- llvm/Support/Casting.h - Allow flexible, checked, casts --*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the isa<X>(), cast<X>(), dyn_cast<X>(),
// cast_if_present<X>(), and dyn_cast_if_present<X>() templates.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SUPPORT_CASTING_H
#define LLVM_SUPPORT_CASTING_H

#include "llvm/Support/Compiler.h"
#include "llvm/Support/type_traits.h"
#include <cassert>
#include <memory>
#include <optional>
#include <type_traits>

namespace llvm {

//===----------------------------------------------------------------------===//
// simplify_type
//===----------------------------------------------------------------------===//

/// 定义一个可以通过智能指针专门化的模板，以反映它们自动取消引用的事实，
/// 并且不参与模板选择过程......默认实现是noop。
/// Define a template that can be specialized by smart pointers to reflect the
/// fact that they are automatically dereferenced, and are not involved with the
/// template selection process...  the default implementation is a noop.
// TODO：重命名它和/或用其他类型转换特征替换它。
// TODO: rename this and/or replace it with other cast traits.
template <typename From> struct simplify_type {
  // 这代表的真正类型...
  using SimpleType = From; // The real type this represents...

  // 直接返回入参的值，获取真实值的访问器...
  // An accessor to get the real value...
  static SimpleType &getSimplifiedValue(From &Val) { return Val; }
};

// 特化版本：const From
template <typename From> struct simplify_type<const From> {
  // 先去掉 const，然后获取其简化后的类型。
  using NonConstSimpleType = typename simplify_type<From>::SimpleType;
  // 对于非指针类型添加 const，而对于指针类型则仅对指向的对象添加 const。
  using SimpleType = typename add_const_past_pointer<NonConstSimpleType>::type;
  // 通过 add_lvalue_reference_if_not_pointer 确保返回类型是引用（除非是指针）。
  using RetType =
      typename add_lvalue_reference_if_not_pointer<SimpleType>::type;

  // 去掉 const 描述符后，返回入参值
  static RetType getSimplifiedValue(const From &Val) {
    // 去掉 const 后调用非 const 版本的简化逻辑。
    return simplify_type<From>::getSimplifiedValue(const_cast<From &>(Val));
  }
};

// TODO: add this namespace once everyone is switched to using the new
//       interface.
// namespace detail {

//===----------------------------------------------------------------------===//
// isa_impl
//===----------------------------------------------------------------------===//

// isa<X> 实现的核心就在这里；To 和 From 应该是类名。
// 此模板可以特化，以定制 isa<> 的实现，而无需从头重写。
// The core of the implementation of isa<X> is here; To and From should be
// the names of classes.  This template can be specialized to customize the
// implementation of isa<> without rewriting it from scratch.
template <typename To, typename From, typename Enabler = void> struct isa_impl {
  static inline bool doit(const From &Val) { return To::classof(&Val); }
};

// Always allow upcasts, and perform no dynamic check for them.
template <typename To, typename From>
struct isa_impl<To, From, std::enable_if_t<std::is_base_of_v<To, From>>> {
  static inline bool doit(const From &) { return true; }
};

template <typename To, typename From> struct isa_impl_cl {
  static inline bool doit(const From &Val) {
    return isa_impl<To, From>::doit(Val);
  }
};

template <typename To, typename From> struct isa_impl_cl<To, const From> {
  static inline bool doit(const From &Val) {
    return isa_impl<To, From>::doit(Val);
  }
};

template <typename To, typename From>
struct isa_impl_cl<To, const std::unique_ptr<From>> {
  static inline bool doit(const std::unique_ptr<From> &Val) {
    assert(Val && "isa<> used on a null pointer");
    return isa_impl_cl<To, From>::doit(*Val);
  }
};

template <typename To, typename From> struct isa_impl_cl<To, From *> {
  static inline bool doit(const From *Val) {
    assert(Val && "isa<> used on a null pointer");
    return isa_impl<To, From>::doit(*Val);
  }
};

template <typename To, typename From> struct isa_impl_cl<To, From *const> {
  static inline bool doit(const From *Val) {
    assert(Val && "isa<> used on a null pointer");
    return isa_impl<To, From>::doit(*Val);
  }
};

template <typename To, typename From> struct isa_impl_cl<To, const From *> {
  static inline bool doit(const From *Val) {
    assert(Val && "isa<> used on a null pointer");
    return isa_impl<To, From>::doit(*Val);
  }
};

template <typename To, typename From>
struct isa_impl_cl<To, const From *const> {
  static inline bool doit(const From *Val) {
    assert(Val && "isa<> used on a null pointer");
    return isa_impl<To, From>::doit(*Val);
  }
};

template <typename To, typename From, typename SimpleFrom>
struct isa_impl_wrap {
  // 当 From != SimplifiedType 时，我们可以使用 simplify_type 模板进一步简化类型。
  // 如果From和SimpleFrom类型不一样，递归简化类型，最终调用到下面的特化实现
  // When From != SimplifiedType, we can simplify the type some more by using
  // the simplify_type template.
  static bool doit(const From &Val) {
    return isa_impl_wrap<To, SimpleFrom,
                         typename simplify_type<SimpleFrom>::SimpleType>::
        doit(simplify_type<const From>::getSimplifiedValue(Val));
  }
};

template <typename To, typename FromTy>
struct isa_impl_wrap<To, FromTy, FromTy> {
  // 当 From == SimpleType 时，我们将获得尽可能简单的结果。
  // When From == SimpleType, we are as simple as we are going to get.
  static bool doit(const FromTy &Val) {
    return isa_impl_cl<To, FromTy>::doit(Val);
  }
};

//===----------------------------------------------------------------------===//
// cast_retty + cast_retty_impl
//===----------------------------------------------------------------------===//

template <class To, class From> struct cast_retty;

// Calculate what type the 'cast' function should return, based on a requested
// type of To and a source type of From.
template <class To, class From> struct cast_retty_impl {
  using ret_type = To &; // Normal case, return Ty&
};
template <class To, class From> struct cast_retty_impl<To, const From> {
  using ret_type = const To &; // Normal case, return Ty&
};

template <class To, class From> struct cast_retty_impl<To, From *> {
  using ret_type = To *; // Pointer arg case, return Ty*
};

template <class To, class From> struct cast_retty_impl<To, const From *> {
  using ret_type = const To *; // Constant pointer arg case, return const Ty*
};

template <class To, class From> struct cast_retty_impl<To, const From *const> {
  using ret_type = const To *; // Constant pointer arg case, return const Ty*
};

template <class To, class From>
struct cast_retty_impl<To, std::unique_ptr<From>> {
private:
  using PointerType = typename cast_retty_impl<To, From *>::ret_type;
  using ResultType = std::remove_pointer_t<PointerType>;

public:
  using ret_type = std::unique_ptr<ResultType>;
};

template <class To, class From, class SimpleFrom> struct cast_retty_wrap {
  // 当简化类型和源类型不一样时，使用类型简化器来减少类型，
  // 然后重用 cast_retty_impl 来获取结果类型。
  // When the simplified type and the from type are not the same, use the type
  // simplifier to reduce the type, then reuse cast_retty_impl to get the
  // resultant type.
  using ret_type = typename cast_retty<To, SimpleFrom>::ret_type;
};

template <class To, class FromTy> struct cast_retty_wrap<To, FromTy, FromTy> {
  // When the simplified type is equal to the from type, use it directly.
  using ret_type = typename cast_retty_impl<To, FromTy>::ret_type;
};

template <class To, class From> struct cast_retty {
  using ret_type = typename cast_retty_wrap<
      To, From, typename simplify_type<From>::SimpleType>::ret_type;
};

//===----------------------------------------------------------------------===//
// cast_convert_val
//===----------------------------------------------------------------------===//

// 确保使用可以通过智能指针专门化的 simplify_type 模板转换非简单值...
// Ensure the non-simple values are converted using the simplify_type template
// that may be specialized by smart pointers...
//
template <class To, class From, class SimpleFrom> struct cast_convert_val {
  // 这不是一个简单的类型，使用模板来简化它...
  // This is not a simple type, use the template to simplify it...
  static typename cast_retty<To, From>::ret_type doit(const From &Val) {
    return cast_convert_val<To, SimpleFrom,
                            typename simplify_type<SimpleFrom>::SimpleType>::
        doit(simplify_type<From>::getSimplifiedValue(const_cast<From &>(Val)));
  }
};

template <class To, class FromTy> struct cast_convert_val<To, FromTy, FromTy> {
  // 如果它是一个引用，则切换到一个指针进行转换，然后取消引用它。
  // If it's a reference, switch to a pointer to do the cast and then deref it.
  static typename cast_retty<To, FromTy>::ret_type doit(const FromTy &Val) {
    return *(std::remove_reference_t<typename cast_retty<To, FromTy>::ret_type>
                 *)&const_cast<FromTy &>(Val);
  }
};

template <class To, class FromTy>
struct cast_convert_val<To, FromTy *, FromTy *> {
  // 如果它是一个指针，我们可以直接使用 c 风格的转换。
  // To: 目标类型
  // FromTy *: 源类型（指针类型），这里同时作为第三个模板参数（SimpleFrom）表示这是最简单的形式
  // If it's a pointer, we can use c-style casting directly.
  static typename cast_retty<To, FromTy *>::ret_type doit(const FromTy *Val) {
    // 通过 cast_retty 元函数计算出的返回类型
    return (typename cast_retty<To, FromTy *>::ret_type) const_cast<FromTy *>(
        Val);
  }
};

//===----------------------------------------------------------------------===//
// is_simple_type
//===----------------------------------------------------------------------===//

/// 用于检查类型 X 是否是"简单类型"
template <class X> struct is_simple_type {
  /**
   * 这是一个类型萃取(trait)模板，LLVM中用于获取类型X的简化表示
   * 对于需要简化的类型，会特化 simplify_type并 提供 SimpleType 成员类型
   * 对于不需要简化的类型，SimpleType 就是X本身
  */
  static const bool value =
      std::is_same_v<X, typename simplify_type<X>::SimpleType>;
};

// } // namespace detail

//===----------------------------------------------------------------------===//
// CastIsPossible
//===----------------------------------------------------------------------===//

/// 此结构体提供了一种检查给定类型转换是否可行的方法。它提供了一个名为 isPossible 的静态函数，
/// 用于检查类型转换是否可以执行。应按如下方式重写它：
/// This struct provides a way to check if a given cast is possible. It provides
/// a static function called isPossible that is used to check if a cast can be
/// performed. It should be overridden like this:
///
/// template<> struct CastIsPossible<foo, bar> {
///   static inline bool isPossible(const bar &b) {
///     return bar.isFoo();
///   }
/// };
template <typename To, typename From, typename Enable = void>
struct CastIsPossible {
  static inline bool isPossible(const From &f) {
    return isa_impl_wrap<
        To, const From,
        typename simplify_type<const From>::SimpleType>::doit(f);
  }
};

// Needed for optional unwrapping. This could be implemented with isa_impl, but
// we want to implement things in the new method and move old implementations
// over. In fact, some of the isa_impl templates should be moved over to
// CastIsPossible.
template <typename To, typename From>
struct CastIsPossible<To, std::optional<From>> {
  static inline bool isPossible(const std::optional<From> &f) {
    assert(f && "CastIsPossible::isPossible called on a nullopt!");
    return isa_impl_wrap<
        To, const From,
        typename simplify_type<const From>::SimpleType>::doit(*f);
  }
};

/// Upcasting (from derived to base) and casting from a type to itself should
/// always be possible.
template <typename To, typename From>
struct CastIsPossible<To, From, std::enable_if_t<std::is_base_of_v<To, From>>> {
  static inline bool isPossible(const From &f) { return true; }
};

//===----------------------------------------------------------------------===//
// Cast traits
//===----------------------------------------------------------------------===//

/// All of these cast traits are meant to be implementations for useful casts
/// that users may want to use that are outside the standard behavior. An
/// example of how to use a special cast called `CastTrait` is:
///
/// template<> struct CastInfo<foo, bar> : public CastTrait<foo, bar> {};
///
/// Essentially, if your use case falls directly into one of the use cases
/// supported by a given cast trait, simply inherit your special CastInfo
/// directly from one of these to avoid having to reimplement the boilerplate
/// `isPossible/castFailed/doCast/doCastIfPossible`. A cast trait can also
/// provide a subset of those functions.

/// This cast trait just provides castFailed for the specified `To` type to make
/// CastInfo specializations more declarative. In order to use this, the target
/// result type must be `To` and `To` must be constructible from `nullptr`.
template <typename To> struct NullableValueCastFailed {
  static To castFailed() { return To(nullptr); }
};

/// This cast trait just provides the default implementation of doCastIfPossible
/// to make CastInfo specializations more declarative. The `Derived` template
/// parameter *must* be provided for forwarding castFailed and doCast.
template <typename To, typename From, typename Derived>
struct DefaultDoCastIfPossible {
  static To doCastIfPossible(From f) {
    if (!Derived::isPossible(f))
      return Derived::castFailed();
    return Derived::doCast(f);
  }
};

namespace detail {
/// A helper to derive the type to use with `Self` for cast traits, when the
/// provided CRTP derived type is allowed to be void.
template <typename OptionalDerived, typename Default>
using SelfType = std::conditional_t<std::is_same_v<OptionalDerived, void>,
                                    Default, OptionalDerived>;
} // namespace detail

/// This cast trait provides casting for the specific case of casting to a
/// value-typed object from a pointer-typed object. Note that `To` must be
/// nullable/constructible from a pointer to `From` to use this cast.
template <typename To, typename From, typename Derived = void>
struct ValueFromPointerCast
    : public CastIsPossible<To, From *>,
      public NullableValueCastFailed<To>,
      public DefaultDoCastIfPossible<
          To, From *,
          detail::SelfType<Derived, ValueFromPointerCast<To, From>>> {
  static inline To doCast(From *f) { return To(f); }
};

/// This cast trait provides std::unique_ptr casting. It has the semantics of
/// moving the contents of the input unique_ptr into the output unique_ptr
/// during the cast. It's also a good example of how to implement a move-only
/// cast.
template <typename To, typename From, typename Derived = void>
struct UniquePtrCast : public CastIsPossible<To, From *> {
  using Self = detail::SelfType<Derived, UniquePtrCast<To, From>>;
  using CastResultType = std::unique_ptr<
      std::remove_reference_t<typename cast_retty<To, From>::ret_type>>;

  static inline CastResultType doCast(std::unique_ptr<From> &&f) {
    return CastResultType((typename CastResultType::element_type *)f.release());
  }

  static inline CastResultType castFailed() { return CastResultType(nullptr); }

  static inline CastResultType doCastIfPossible(std::unique_ptr<From> &f) {
    if (!Self::isPossible(f.get()))
      return castFailed();
    return doCast(std::move(f));
  }
};

/// This cast trait provides std::optional<T> casting. This means that if you
/// have a value type, you can cast it to another value type and have dyn_cast
/// return an std::optional<T>.
template <typename To, typename From, typename Derived = void>
struct OptionalValueCast
    : public CastIsPossible<To, From>,
      public DefaultDoCastIfPossible<
          std::optional<To>, From,
          detail::SelfType<Derived, OptionalValueCast<To, From>>> {
  static inline std::optional<To> castFailed() { return std::optional<To>{}; }

  static inline std::optional<To> doCast(const From &f) { return To(f); }
};

/// Provides a cast trait that strips `const` from types to make it easier to
/// implement a const-version of a non-const cast. It just removes boilerplate
/// and reduces the amount of code you as the user need to implement. You can
/// use it like this:
///
/// template<> struct CastInfo<foo, bar> {
///   ...verbose implementation...
/// };
///
/// template<> struct CastInfo<foo, const bar> : public
///        ConstStrippingForwardingCast<foo, const bar, CastInfo<foo, bar>> {};
///
template <typename To, typename From, typename ForwardTo>
struct ConstStrippingForwardingCast {
  // Remove the pointer if it exists, then we can get rid of consts/volatiles.
  using DecayedFrom = std::remove_cv_t<std::remove_pointer_t<From>>;
  // Now if it's a pointer, add it back. Otherwise, we want a ref.
  using NonConstFrom =
      std::conditional_t<std::is_pointer_v<From>, DecayedFrom *, DecayedFrom &>;

  static inline bool isPossible(const From &f) {
    return ForwardTo::isPossible(const_cast<NonConstFrom>(f));
  }

  static inline decltype(auto) castFailed() { return ForwardTo::castFailed(); }

  static inline decltype(auto) doCast(const From &f) {
    return ForwardTo::doCast(const_cast<NonConstFrom>(f));
  }

  static inline decltype(auto) doCastIfPossible(const From &f) {
    return ForwardTo::doCastIfPossible(const_cast<NonConstFrom>(f));
  }
};

/// Provides a cast trait that uses a defined pointer to pointer cast as a base
/// for reference-to-reference casts. Note that it does not provide castFailed
/// and doCastIfPossible because a pointer-to-pointer cast would likely just
/// return `nullptr` which could cause nullptr dereference. You can use it like
/// this:
///
///   template <> struct CastInfo<foo, bar *> { ... verbose implementation... };
///
///   template <>
///   struct CastInfo<foo, bar>
///       : public ForwardToPointerCast<foo, bar, CastInfo<foo, bar *>> {};
///
template <typename To, typename From, typename ForwardTo>
struct ForwardToPointerCast {
  static inline bool isPossible(const From &f) {
    return ForwardTo::isPossible(&f);
  }

  static inline decltype(auto) doCast(const From &f) {
    return *ForwardTo::doCast(&f);
  }
};

//===----------------------------------------------------------------------===//
// CastInfo
//===----------------------------------------------------------------------===//

/// This struct provides a method for customizing the way a cast is performed.
/// It inherits from CastIsPossible, to support the case of declaring many
/// CastIsPossible specializations without having to specialize the full
/// CastInfo.
///
/// In order to specialize different behaviors, specify different functions in
/// your CastInfo specialization.
/// For isa<> customization, provide:
///
///   `static bool isPossible(const From &f)`
///
/// For cast<> customization, provide:
///
///  `static To doCast(const From &f)`
///
/// For dyn_cast<> and the *_if_present<> variants' customization, provide:
///
///  `static To castFailed()` and `static To doCastIfPossible(const From &f)`
///
/// Your specialization might look something like this:
///
///  template<> struct CastInfo<foo, bar> : public CastIsPossible<foo, bar> {
///    static inline foo doCast(const bar &b) {
///      return foo(const_cast<bar &>(b));
///    }
///    static inline foo castFailed() { return foo(); }
///    static inline foo doCastIfPossible(const bar &b) {
///      if (!CastInfo<foo, bar>::isPossible(b))
///        return castFailed();
///      return doCast(b);
///    }
///  };

// CastInfo 的默认实现目前不使用强制类型转换特性，
// 因为根据当前预期的强制类型转换行为以及 cast_retty 的工作方式，我们需要在所有地方指定类型。
// 新的用例可以并且应该尽可能利用强制类型转换特性！
// The default implementations of CastInfo don't use cast traits for now because
// we need to specify types all over the place due to the current expected
// casting behavior and the way cast_retty works. New use cases can and should
// take advantage of the cast traits whenever possible!

template <typename To, typename From, typename Enable = void>
struct CastInfo : public CastIsPossible<To, From> {
  using Self = CastInfo<To, From, Enable>;

  using CastReturnType = typename cast_retty<To, From>::ret_type;

  static inline CastReturnType doCast(const From &f) {
    // 使用cast_convert_val递归简化类型，最终执行C风格指针转换或引用解引用
    return cast_convert_val<
        To, From,
        typename simplify_type<From>::SimpleType>::doit(const_cast<From &>(f));
  }

  // 这假设您可以从“nullptr”构造强制转换返回类型。
  // 这主要是为了支持遗留用例 - 如果您不想要这种行为，您应该为您的用例专门设计 CastInfo。
  // This assumes that you can construct the cast return type from `nullptr`.
  // This is largely to support legacy use cases - if you don't want this
  // behavior you should specialize CastInfo for your use case.
  static inline CastReturnType castFailed() { return CastReturnType(nullptr); }

  static inline CastReturnType doCastIfPossible(const From &f) {
    // 检查类型是否兼容
    if (!Self::isPossible(f)) {
      return castFailed();
    }

    // 执行实际转换
    return doCast(f);
  }
};

/// 此结构体为 CastInfo 提供了一个重载，其中 From 定义了 simplify_type。
/// 它只会转发到具有简化类型/值的相应 CastInfo，因此您无需同时实现两者。
/// This struct provides an overload for CastInfo where From has simplify_type
/// defined. This simply forwards to the appropriate CastInfo with the
/// simplified type/value, so you don't have to implement both.
template <typename To, typename From>
struct CastInfo<To, From, std::enable_if_t<!is_simple_type<From>::value>> {
  using Self = CastInfo<To, From>;
  using SimpleFrom = typename simplify_type<From>::SimpleType;
  using SimplifiedSelf = CastInfo<To, SimpleFrom>;

  static inline bool isPossible(From &f) {
    return SimplifiedSelf::isPossible(
        simplify_type<From>::getSimplifiedValue(f));
  }

  static inline decltype(auto) doCast(From &f) {
    return SimplifiedSelf::doCast(simplify_type<From>::getSimplifiedValue(f));
  }

  static inline decltype(auto) castFailed() {
    return SimplifiedSelf::castFailed();
  }

  static inline decltype(auto) doCastIfPossible(From &f) {
    return SimplifiedSelf::doCastIfPossible(
        simplify_type<From>::getSimplifiedValue(f));
  }
};

//===----------------------------------------------------------------------===//
// Pre-specialized CastInfo
//===----------------------------------------------------------------------===//

/// Provide a CastInfo specialized for std::unique_ptr.
template <typename To, typename From>
struct CastInfo<To, std::unique_ptr<From>> : public UniquePtrCast<To, From> {};

/// Provide a CastInfo specialized for std::optional<From>. It's assumed that if
/// the input is std::optional<From> that the output can be std::optional<To>.
/// If that's not the case, specialize CastInfo for your use case.
template <typename To, typename From>
struct CastInfo<To, std::optional<From>> : public OptionalValueCast<To, From> {
};

/// isa<X> - 如果模板的参数是模板类型参数之一的实例，则返回 true。用法如下：
/// isa<X> - Return true if the parameter to the template is an instance of one
/// of the template type arguments.  Used like this:
///
///  if (isa<Type>(myVal)) { ... }
///  if (isa<Type0, Type1, Type2>(myVal)) { ... }
template <typename To, typename From>
[[nodiscard]] inline bool isa(const From &Val) {
  return CastInfo<To, const From>::isPossible(Val);
}

template <typename First, typename Second, typename... Rest, typename From>
[[nodiscard]] inline bool isa(const From &Val) {
  return isa<First>(Val) || isa<Second, Rest...>(Val);
}

/// cast<X> - Return the argument parameter cast to the specified type.  This
/// casting operator asserts that the type is correct, so it does not return
/// null on failure.  It does not allow a null argument (use cast_if_present for
/// that). It is typically used like this:
///
///  cast<Instruction>(myVal)->getParent()

template <typename To, typename From>
[[nodiscard]] inline decltype(auto) cast(const From &Val) {
  assert(isa<To>(Val) && "cast<Ty>() argument of incompatible type!");
  return CastInfo<To, const From>::doCast(Val);
}

template <typename To, typename From>
[[nodiscard]] inline decltype(auto) cast(From &Val) {
  assert(isa<To>(Val) && "cast<Ty>() argument of incompatible type!");
  return CastInfo<To, From>::doCast(Val);
}

template <typename To, typename From>
[[nodiscard]] inline decltype(auto) cast(From *Val) {
  assert(isa<To>(Val) && "cast<Ty>() argument of incompatible type!");
  return CastInfo<To, From *>::doCast(Val);
}

template <typename To, typename From>
[[nodiscard]] inline decltype(auto) cast(std::unique_ptr<From> &&Val) {
  assert(isa<To>(Val) && "cast<Ty>() argument of incompatible type!");
  return CastInfo<To, std::unique_ptr<From>>::doCast(std::move(Val));
}

//===----------------------------------------------------------------------===//
// ValueIsPresent
//===----------------------------------------------------------------------===//

template <typename T>
constexpr bool IsNullable =
    std::is_pointer_v<T> || std::is_constructible_v<T, std::nullptr_t>;

/// ValueIsPresent provides a way to check if a value is, well, present. For
/// pointers, this is the equivalent of checking against nullptr, for Optionals
/// this is the equivalent of checking hasValue(). It also provides a method for
/// unwrapping a value (think calling .value() on an optional).

// Generic values can't *not* be present.
template <typename T, typename Enable = void> struct ValueIsPresent {
  using UnwrappedType = T;
  static inline bool isPresent(const T &t) { return true; }
  static inline decltype(auto) unwrapValue(T &t) { return t; }
};

// Optional provides its own way to check if something is present.
template <typename T> struct ValueIsPresent<std::optional<T>> {
  using UnwrappedType = T;
  static inline bool isPresent(const std::optional<T> &t) {
    return t.has_value();
  }
  static inline decltype(auto) unwrapValue(std::optional<T> &t) { return *t; }
};

// If something is "nullable" then we just compare it to nullptr to see if it
// exists.
template <typename T>
struct ValueIsPresent<T, std::enable_if_t<IsNullable<T>>> {
  using UnwrappedType = T;
  static inline bool isPresent(const T &t) { return t != T(nullptr); }
  static inline decltype(auto) unwrapValue(T &t) { return t; }
};

namespace detail {
// Convenience function we can use to check if a value is present. Because of
// simplify_type, we have to call it on the simplified type for now.
template <typename T> inline bool isPresent(const T &t) {
  return ValueIsPresent<typename simplify_type<T>::SimpleType>::isPresent(
      simplify_type<T>::getSimplifiedValue(const_cast<T &>(t)));
}

// Convenience function we can use to unwrap a value.
template <typename T> inline decltype(auto) unwrapValue(T &t) {
  return ValueIsPresent<T>::unwrapValue(t);
}
} // namespace detail

/// dyn_cast<X> - Return the argument parameter cast to the specified type. This
/// casting operator returns null if the argument is of the wrong type, so it
/// can be used to test for a type as well as cast if successful. The value
/// passed in must be present, if not, use dyn_cast_if_present. This should be
/// used in the context of an if statement like this:
///
///  if (const Instruction *I = dyn_cast<Instruction>(myVal)) { ... }

template <typename To, typename From>
[[nodiscard]] inline decltype(auto) dyn_cast(const From &Val) {
  assert(detail::isPresent(Val) && "dyn_cast on a non-existent value");
  return CastInfo<To, const From>::doCastIfPossible(Val);
}

template <typename To, typename From>
[[nodiscard]] inline decltype(auto) dyn_cast(From &Val) {
  assert(detail::isPresent(Val) && "dyn_cast on a non-existent value");
  return CastInfo<To, From>::doCastIfPossible(Val);
}

template <typename To, typename From>
[[nodiscard]] inline decltype(auto) dyn_cast(From *Val) {
  // 首先检查指针是否有效(非空)
  assert(detail::isPresent(Val) && "dyn_cast on a non-existent value");

  return CastInfo<To, From *>::doCastIfPossible(Val);
}

template <typename To, typename From>
[[nodiscard]] inline decltype(auto) dyn_cast(std::unique_ptr<From> &Val) {
  assert(detail::isPresent(Val) && "dyn_cast on a non-existent value");
  return CastInfo<To, std::unique_ptr<From>>::doCastIfPossible(Val);
}

/// isa_and_present<X> - Functionally identical to isa, except that a null value
/// is accepted.
template <typename... X, class Y>
[[nodiscard]] inline bool isa_and_present(const Y &Val) {
  if (!detail::isPresent(Val))
    return false;
  return isa<X...>(Val);
}

template <typename... X, class Y>
[[nodiscard]] inline bool isa_and_nonnull(const Y &Val) {
  return isa_and_present<X...>(Val);
}

/// cast_if_present<X> - Functionally identical to cast, except that a null
/// value is accepted.
template <class X, class Y>
[[nodiscard]] inline auto cast_if_present(const Y &Val) {
  if (!detail::isPresent(Val))
    return CastInfo<X, const Y>::castFailed();
  assert(isa<X>(Val) && "cast_if_present<Ty>() argument of incompatible type!");
  return cast<X>(detail::unwrapValue(Val));
}

template <class X, class Y> [[nodiscard]] inline auto cast_if_present(Y &Val) {
  if (!detail::isPresent(Val))
    return CastInfo<X, Y>::castFailed();
  assert(isa<X>(Val) && "cast_if_present<Ty>() argument of incompatible type!");
  return cast<X>(detail::unwrapValue(Val));
}

template <class X, class Y> [[nodiscard]] inline auto cast_if_present(Y *Val) {
  if (!detail::isPresent(Val))
    return CastInfo<X, Y *>::castFailed();
  assert(isa<X>(Val) && "cast_if_present<Ty>() argument of incompatible type!");
  return cast<X>(detail::unwrapValue(Val));
}

template <class X, class Y>
[[nodiscard]] inline auto cast_if_present(std::unique_ptr<Y> &&Val) {
  if (!detail::isPresent(Val))
    return UniquePtrCast<X, Y>::castFailed();
  return UniquePtrCast<X, Y>::doCast(std::move(Val));
}

// Provide a forwarding from cast_or_null to cast_if_present for current
// users. This is deprecated and will be removed in a future patch, use
// cast_if_present instead.
template <class X, class Y> auto cast_or_null(const Y &Val) {
  return cast_if_present<X>(Val);
}

template <class X, class Y> auto cast_or_null(Y &Val) {
  return cast_if_present<X>(Val);
}

template <class X, class Y> auto cast_or_null(Y *Val) {
  return cast_if_present<X>(Val);
}

template <class X, class Y> auto cast_or_null(std::unique_ptr<Y> &&Val) {
  return cast_if_present<X>(std::move(Val));
}

/// dyn_cast_if_present<X> - Functionally identical to dyn_cast, except that a
/// null (or none in the case of optionals) value is accepted.
template <class X, class Y> auto dyn_cast_if_present(const Y &Val) {
  if (!detail::isPresent(Val))
    return CastInfo<X, const Y>::castFailed();
  return CastInfo<X, const Y>::doCastIfPossible(detail::unwrapValue(Val));
}

template <class X, class Y> auto dyn_cast_if_present(Y &Val) {
  if (!detail::isPresent(Val))
    return CastInfo<X, Y>::castFailed();
  return CastInfo<X, Y>::doCastIfPossible(detail::unwrapValue(Val));
}

template <class X, class Y> auto dyn_cast_if_present(Y *Val) {
  if (!detail::isPresent(Val))
    return CastInfo<X, Y *>::castFailed();
  return CastInfo<X, Y *>::doCastIfPossible(detail::unwrapValue(Val));
}

// Forwards to dyn_cast_if_present to avoid breaking current users. This is
// deprecated and will be removed in a future patch, use
// cast_if_present instead.
template <class X, class Y> auto dyn_cast_or_null(const Y &Val) {
  return dyn_cast_if_present<X>(Val);
}

template <class X, class Y> auto dyn_cast_or_null(Y &Val) {
  return dyn_cast_if_present<X>(Val);
}

template <class X, class Y> auto dyn_cast_or_null(Y *Val) {
  return dyn_cast_if_present<X>(Val);
}

/// unique_dyn_cast<X> - Given a unique_ptr<Y>, try to return a unique_ptr<X>,
/// taking ownership of the input pointer iff isa<X>(Val) is true.  If the
/// cast is successful, From refers to nullptr on exit and the casted value
/// is returned.  If the cast is unsuccessful, the function returns nullptr
/// and From is unchanged.
template <class X, class Y>
[[nodiscard]] inline typename CastInfo<X, std::unique_ptr<Y>>::CastResultType
unique_dyn_cast(std::unique_ptr<Y> &Val) {
  if (!isa<X>(Val))
    return nullptr;
  return cast<X>(std::move(Val));
}

template <class X, class Y>
[[nodiscard]] inline auto unique_dyn_cast(std::unique_ptr<Y> &&Val) {
  return unique_dyn_cast<X, Y>(Val);
}

// unique_dyn_cast_or_null<X> - Functionally identical to unique_dyn_cast,
// except that a null value is accepted.
template <class X, class Y>
[[nodiscard]] inline typename CastInfo<X, std::unique_ptr<Y>>::CastResultType
unique_dyn_cast_or_null(std::unique_ptr<Y> &Val) {
  if (!Val)
    return nullptr;
  return unique_dyn_cast<X, Y>(Val);
}

template <class X, class Y>
[[nodiscard]] inline auto unique_dyn_cast_or_null(std::unique_ptr<Y> &&Val) {
  return unique_dyn_cast_or_null<X, Y>(Val);
}

//===----------------------------------------------------------------------===//
// Isa Predicates
//===----------------------------------------------------------------------===//

/// These are wrappers over isa* function that allow them to be used in generic
/// algorithms such as `llvm:all_of`, `llvm::none_of`, etc. This is accomplished
/// by exposing the isa* functions through function objects with a generic
/// function call operator.

namespace detail {
template <typename... Types> struct IsaCheckPredicate {
  template <typename T> [[nodiscard]] bool operator()(const T &Val) const {
    return isa<Types...>(Val);
  }
};

template <typename... Types> struct IsaAndPresentCheckPredicate {
  template <typename T> [[nodiscard]] bool operator()(const T &Val) const {
    return isa_and_present<Types...>(Val);
  }
};
} // namespace detail

/// Function object wrapper for the `llvm::isa` type check. The function call
/// operator returns true when the value can be cast to any type in `Types`.
/// Example:
/// ```
/// SmallVector<Type> myTypes = ...;
/// if (llvm::all_of(myTypes, llvm::IsaPred<VectorType>))
///   ...
/// ```
template <typename... Types>
inline constexpr detail::IsaCheckPredicate<Types...> IsaPred{};

/// Function object wrapper for the `llvm::isa_and_present` type check. The
/// function call operator returns true when the value can be cast to any type
/// in `Types`, or if the value is not present (e.g., nullptr). Example:
/// ```
/// SmallVector<Type> myTypes = ...;
/// if (llvm::all_of(myTypes, llvm::IsaAndPresentPred<VectorType>))
///   ...
/// ```
template <typename... Types>
inline constexpr detail::IsaAndPresentCheckPredicate<Types...>
    IsaAndPresentPred{};

} // end namespace llvm

#endif // LLVM_SUPPORT_CASTING_H
