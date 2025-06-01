//===- Intrinsics.h - LLVM Intrinsic Function Handling ----------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines a set of enums which allow processing of intrinsic
// functions.  Values of these enum types are returned by
// Function::getIntrinsicID.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_INTRINSICS_H
#define LLVM_IR_INTRINSICS_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/TypeSize.h"
#include <optional>
#include <string>

namespace llvm {

class Type;
class FunctionType;
class Function;
class LLVMContext;
class Module;
class AttributeList;

/// 该命名空间包含一个枚举类型，其中包含LLVM已知的所有
/// 固有/内置函数对应的枚举值。这些枚举值可通过
/// Function::getIntrinsicID() 方法获取。
///
/// This namespace contains an enum with a value for every intrinsic/builtin
/// function known by LLVM. The enum values are returned by
/// Function::getIntrinsicID().
namespace Intrinsic {
  // noalias 内部函数的参数抽象表示
  // Abstraction for the arguments of the noalias intrinsics
  static const int NoAliasScopeDeclScopeArg = 0;

  // 内部函数ID类型。这是一个不透明类型定义，用于将枚举拆分为目标特定的枚举
  // Intrinsic ID type. This is an opaque typedef to facilitate splitting up
  // the enum into target-specific enums.
  typedef unsigned ID;

  enum IndependentIntrinsics : unsigned {
    not_intrinsic = 0, // Must be zero 必须为零值

  // 获取从Intrinsics.td生成的内部函数枚举值
  // Get the intrinsic enums generated from Intrinsics.td
#define GET_INTRINSIC_ENUM_VALUES
#include "llvm/IR/IntrinsicEnums.inc"
#undef GET_INTRINSIC_ENUM_VALUES
  };

  /// 返回内部函数的LLVM名称（如"llvm.ppc.altivec.lvx"）。
  /// 注意：此版本用于无重载的内部函数。如需处理重载，请使用另一版本。
  /// Return the LLVM name for an intrinsic, such as "llvm.ppc.altivec.lvx".
  /// Note, this version is for intrinsics with no overloads.  Use the other
  /// version of getName if overloads are required.
  StringRef getName(ID id);

  /// 返回内部函数的基础名称（不含重载类型编码），例如"llvm.ssa.copy"。
  /// Return the LLVM name for an intrinsic, without encoded types for
  /// overloading, such as "llvm.ssa.copy".
  StringRef getBaseName(ID id);

  /// 返回内部函数的完整名称（支持重载版本），
  /// 例如"llvm.ppc.altivec.lvx"或"llvm.ssa.copy.p0s_s.1"。
  /// 注意：此版本效率低于StringRef版本。若无重载需求，建议使用StringRef版本。
  /// 若涉及匿名类型，将计算函数类型。提供FT参数可避免此计算。
  ///
  /// Return the LLVM name for an intrinsic, such as "llvm.ppc.altivec.lvx" or
  /// "llvm.ssa.copy.p0s_s.1". Note, this version of getName supports overloads.
  /// This is less efficient than the StringRef version of this function.  If no
  /// overloads are required, it is safe to use this version, but better to use
  /// the StringRef version. If one of the types is based on an unnamed type, a
  /// function type will be computed. Providing FT will avoid this computation.
  std::string getName(ID Id, ArrayRef<Type *> Tys, Module *M,
                      FunctionType *FT = nullptr);

  /// 返回内部函数名称（特殊版本，仅供LLVMIntrinsicCopyOverloadedName使用）。
  /// 仅支持基于命名类型的重载。
  /// Return the LLVM name for an intrinsic. This is a special version only to
  /// be used by LLVMIntrinsicCopyOverloadedName. It only supports overloads
  /// based on named types.
  std::string getNameNoUnnamedTypes(ID Id, ArrayRef<Type *> Tys);

  /// 返回内部函数的函数类型
  /// Return the function type for an intrinsic.
  FunctionType *getType(LLVMContext &Context, ID id,
                        ArrayRef<Type *> Tys = std::nullopt);

  /// 判断内部函数是否支持重载
  /// Returns true if the intrinsic can be overloaded.
  bool isOverloaded(ID id);

  /// 返回内部函数的属性集
  /// Return the attributes for an intrinsic.
  AttributeList getAttributes(LLVMContext &C, ID id);

  /// 创建或获取LLVM内部函数声明
  ///
  /// Tys参数用于处理类型重载的内部函数（如使用iAny/fAny/vAny/iPTRAny）。
  /// 对于重载内部函数的声明，Tys必须为每个重载类型提供确切的一个类型。
  ///
  /// Create or insert an LLVM Function declaration for an intrinsic, and return
  /// it.
  ///
  /// The Tys parameter is for intrinsics with overloaded types (e.g., those
  /// using iAny, fAny, vAny, or iPTRAny).  For a declaration of an overloaded
  /// intrinsic, Tys must provide exactly one type for each overloaded type in
  /// the intrinsic.
  Function *getDeclaration(Module *M, ID id,
                           ArrayRef<Type *> Tys = std::nullopt);

  /// 在NameTable中二分查找名称。NameTable必须已排序且所有条目以"llvm."开头。
  /// 如果找到完全匹配或点号前缀匹配，返回其索引；否则返回-1。
  ///
  /// Looks up Name in NameTable via binary search. NameTable must be sorted
  /// and all entries must start with "llvm.".  If NameTable contains an exact
  /// match for Name or a prefix of Name followed by a dot, its index in
  /// NameTable is returned. Otherwise, -1 is returned.
  int lookupLLVMIntrinsicByName(ArrayRef<const char *> NameTable,
                                StringRef Name);

  /// 将Clang内置函数名映射到内部函数ID
  /// Map a Clang builtin name to an intrinsic ID.
  ID getIntrinsicForClangBuiltin(const char *Prefix, StringRef BuiltinName);

  /// 将MS内置函数名映射到内部函数ID
  /// Map a MS builtin name to an intrinsic ID.
  ID getIntrinsicForMSBuiltin(const char *Prefix, StringRef BuiltinName);

  /// 判断是否为"约束浮点运算内部函数"
  /// Returns true if the intrinsic ID is for one of the "Constrained
  /// Floating-Point Intrinsics".
  bool isConstrainedFPIntrinsic(ID QID);

  /// 判断是否为需要舍入模式参数的"约束浮点运算内部函数"
  /// Returns true if the intrinsic ID is for one of the "Constrained
  /// Floating-Point Intrinsics" that take rounding mode metadata.
  bool hasConstrainedFPRoundingModeOperand(ID QID);

  /// 这是一个类型描述符，用于说明内部函数的类型要求。
  /// 通过 getIntrinsicInfoTableEntries 函数获取该结构体实例。
  ///
  /// This is a type descriptor which explains the type requirements of an
  /// intrinsic. This is returned by getIntrinsicInfoTableEntries.
  struct IITDescriptor {
    enum IITDescriptorKind {
      Void,
      VarArg,
      MMX,
      Token,
      Metadata,
      Half,
      BFloat,
      Float,
      Double,
      Quad,
      Integer,
      Vector,
      Pointer,
      Struct,
      Argument,
      ExtendArgument,
      TruncArgument,
      HalfVecArgument,
      SameVecWidthArgument,
      VecOfAnyPtrsToElt,
      VecElementArgument,
      Subdivide2Argument,
      Subdivide4Argument,
      VecOfBitcastsToInt,
      AMX,
      PPCQuad,
      AArch64Svcount,
    } Kind;

    union {
      unsigned Integer_Width;
      unsigned Float_Width;
      unsigned Pointer_AddressSpace;
      unsigned Struct_NumElements;
      unsigned Argument_Info;
      ElementCount Vector_Width;
    };

    // AK_% : Defined in Intrinsics.td
    enum ArgKind {
#define GET_INTRINSIC_ARGKIND
#include "llvm/IR/IntrinsicEnums.inc"
#undef GET_INTRINSIC_ARGKIND
    };

    unsigned getArgumentNumber() const {
      assert(Kind == Argument || Kind == ExtendArgument ||
             Kind == TruncArgument || Kind == HalfVecArgument ||
             Kind == SameVecWidthArgument || Kind == VecElementArgument ||
             Kind == Subdivide2Argument || Kind == Subdivide4Argument ||
             Kind == VecOfBitcastsToInt);
      return Argument_Info >> 3;
    }
    ArgKind getArgumentKind() const {
      assert(Kind == Argument || Kind == ExtendArgument ||
             Kind == TruncArgument || Kind == HalfVecArgument ||
             Kind == SameVecWidthArgument ||
             Kind == VecElementArgument || Kind == Subdivide2Argument ||
             Kind == Subdivide4Argument || Kind == VecOfBitcastsToInt);
      return (ArgKind)(Argument_Info & 7);
    }

    // VecOfAnyPtrsToElt uses both an overloaded argument (for address space)
    // and a reference argument (for matching vector width and element types)
    unsigned getOverloadArgNumber() const {
      assert(Kind == VecOfAnyPtrsToElt);
      return Argument_Info >> 16;
    }
    unsigned getRefArgNumber() const {
      assert(Kind == VecOfAnyPtrsToElt);
      return Argument_Info & 0xFFFF;
    }

    static IITDescriptor get(IITDescriptorKind K, unsigned Field) {
      IITDescriptor Result = { K, { Field } };
      return Result;
    }

    static IITDescriptor get(IITDescriptorKind K, unsigned short Hi,
                             unsigned short Lo) {
      unsigned Field = Hi << 16 | Lo;
      IITDescriptor Result = {K, {Field}};
      return Result;
    }

    static IITDescriptor getVector(unsigned Width, bool IsScalable) {
      IITDescriptor Result = {Vector, {0}};
      Result.Vector_Width = ElementCount::get(Width, IsScalable);
      return Result;
    }
  };

  /// Return the IIT table descriptor for the specified intrinsic into an array
  /// of IITDescriptors.
  void getIntrinsicInfoTableEntries(ID id, SmallVectorImpl<IITDescriptor> &T);

  enum MatchIntrinsicTypesResult {
    MatchIntrinsicTypes_Match = 0,
    MatchIntrinsicTypes_NoMatchRet = 1,
    MatchIntrinsicTypes_NoMatchArg = 2,
  };

  /// Match the specified function type with the type constraints specified by
  /// the .td file. If the given type is an overloaded type it is pushed to the
  /// ArgTys vector.
  ///
  /// Returns false if the given type matches with the constraints, true
  /// otherwise.
  MatchIntrinsicTypesResult
  matchIntrinsicSignature(FunctionType *FTy, ArrayRef<IITDescriptor> &Infos,
                          SmallVectorImpl<Type *> &ArgTys);

  /// Verify if the intrinsic has variable arguments. This method is intended to
  /// be called after all the fixed arguments have been matched first.
  ///
  /// This method returns true on error.
  bool matchIntrinsicVarArg(bool isVarArg, ArrayRef<IITDescriptor> &Infos);

  /// Gets the type arguments of an intrinsic call by matching type contraints
  /// specified by the .td file. The overloaded types are pushed into the
  /// AgTys vector.
  ///
  /// Returns false if the given ID and function type combination is not a
  /// valid intrinsic call.
  bool getIntrinsicSignature(Intrinsic::ID, FunctionType *FT,
                             SmallVectorImpl<Type *> &ArgTys);

  /// Same as previous, but accepts a Function instead of ID and FunctionType.
  bool getIntrinsicSignature(Function *F, SmallVectorImpl<Type *> &ArgTys);

  // Checks if the intrinsic name matches with its signature and if not
  // returns the declaration with the same signature and remangled name.
  // An existing GlobalValue with the wanted name but with a wrong prototype
  // or of the wrong kind will be renamed by adding ".renamed" to the name.
  std::optional<Function *> remangleIntrinsicFunction(Function *F);

} // End Intrinsic namespace

} // End llvm namespace

#endif
