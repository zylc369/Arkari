//===- llvm/Support/Debug.h - Easy way to add debug output ------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements a handy way of adding debugging information to your
// code, without it being enabled all of the time, and without having to add
// command line options to enable it.
//
// In particular, just wrap your code with the LLVM_DEBUG() macro, and it will
// be enabled automatically if you specify '-debug' on the command-line.
// LLVM_DEBUG() requires the DEBUG_TYPE macro to be defined. Set it to "foo"
// specify that your debug code belongs to class "foo". Be careful that you only
// do this after including Debug.h and not around any #include of headers.
// Headers should define and undef the macro acround the code that needs to use
// the LLVM_DEBUG() macro. Then, on the command line, you can specify
// '-debug-only=foo' to enable JUST the debug information for the foo class.
//
// When compiling without assertions, the -debug-* options and all code in
// LLVM_DEBUG() statements disappears, so it does not affect the runtime of the
// code.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SUPPORT_DEBUG_H
#define LLVM_SUPPORT_DEBUG_H

namespace llvm {

class raw_ostream;

#ifndef NDEBUG

/// isCurrentDebugType - Return true if the specified string is the debug type
/// specified on the command line, or if none was specified on the command line
/// with the -debug-only=X option.
///
bool isCurrentDebugType(const char *Type);

/// setCurrentDebugType - Set the current debug type, as if the -debug-only=X
/// option were specified.  Note that DebugFlag also needs to be set to true for
/// debug output to be produced.
///
void setCurrentDebugType(const char *Type);

/// setCurrentDebugTypes - Set the current debug type, as if the
/// -debug-only=X,Y,Z option were specified. Note that DebugFlag
/// also needs to be set to true for debug output to be produced.
///
void setCurrentDebugTypes(const char **Types, unsigned Count);

/// DEBUG_WITH_TYPE macro - This macro should be used by passes to emit debug
/// information.  If the '-debug' option is specified on the commandline, and if
/// this is a debug build, then the code specified as the option to the macro
/// will be executed.  Otherwise it will not be.  Example:
///
/// DEBUG_WITH_TYPE("bitset", dbgs() << "Bitset contains: " << Bitset << "\n");
///
/// This will emit the debug information if -debug is present, and -debug-only
/// is not specified, or is specified as "bitset".
#define DEBUG_WITH_TYPE(TYPE, X)                                        \
  do { if (::llvm::DebugFlag && ::llvm::isCurrentDebugType(TYPE)) { X; } \
  } while (false)

#else
#define isCurrentDebugType(X) (false)
#define setCurrentDebugType(X) do { (void)(X); } while (false)
#define setCurrentDebugTypes(X, N) do { (void)(X); (void)(N); } while (false)
#define DEBUG_WITH_TYPE(TYPE, X) do { } while (false)
#endif

/// 调试标志 - 当指定'-debug'命令行选项时，该布尔值将被设为 true
///
/// 使用说明：
/// - 建议不要直接引用此变量，而应使用下文提供的 DEBUG 宏
/// - 主要用于控制调试信息的输出行为
///
/// 实现细节：
/// - 由命令行参数解析器自动设置
/// - 默认初始值为false
///
/// This boolean is set to true if the '-debug' command line option
/// is specified.  This should probably not be referenced directly, instead, use
/// the DEBUG macro below.
///
extern bool DebugFlag;

/// 启用调试缓冲 - 该选项默认为关闭状态(false)。若设为开启(true)，
/// 调试流将安装信号处理器来转储所有缓冲的调试输出。
///
/// 功能说明：
/// - 允许客户端在确保不会产生冲突的情况下，有选择地让调试流安装信号处理器
/// - 主要用于需要捕获异常情况下的调试信息时启用
///
/// 注意事项：
/// - 在多线程环境中使用时需确保信号处理的安全性
/// - 可能与其他信号处理器产生冲突，需谨慎使用
///
/// EnableDebugBuffering - This defaults to false.  If true, the debug
/// stream will install signal handlers to dump any buffered debug
/// output.  It allows clients to selectively allow the debug stream
/// to install signal handlers if they are certain there will be no
/// conflict.
///
extern bool EnableDebugBuffering;

/// dbgs() - 返回用于调试信息的 raw_ostream 引用。
/// 若调试功能被禁用则返回 errs()。使用方式：
/// dbgs() << "foo" << "bar";
///
/// dbgs() - This returns a reference to a raw_ostream for debugging
/// messages.  If debugging is disabled it returns errs().  Use it
/// like: dbgs() << "foo" << "bar";
raw_ostream &dbgs();

// DEBUG macro - This macro should be used by passes to emit debug information.
// If the '-debug' option is specified on the commandline, and if this is a
// debug build, then the code specified as the option to the macro will be
// executed.  Otherwise it will not be.  Example:
//
// LLVM_DEBUG(dbgs() << "Bitset contains: " << Bitset << "\n");
//
#define LLVM_DEBUG(X) DEBUG_WITH_TYPE(DEBUG_TYPE, X)

} // end namespace llvm

#endif // LLVM_SUPPORT_DEBUG_H
