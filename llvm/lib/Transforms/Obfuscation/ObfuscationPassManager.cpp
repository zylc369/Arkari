#include "llvm/Transforms/Obfuscation/ObfuscationPassManager.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/IR/Module.h"


#define DEBUG_TYPE "ir-obfuscation"

using namespace llvm;

// 启用 IR 混淆的命令行开关
static cl::opt<bool>
EnableIRObfuscation("irobf", cl::init(false), cl::NotHidden,
                    cl::desc("Enable IR Code Obfuscation."),
                    cl::ZeroOrMore);

// 启用间接分支混淆的开关与级别设置
static cl::opt<bool>



EnableIndirectBr("irobf-indbr", cl::init(false), cl::NotHidden,
                 cl::desc("Enable IR Indirect Branch Obfuscation."),
                 cl::ZeroOrMore);
static cl::opt<uint32_t>
LevelIndirectBr("level-indbr", cl::init(0), cl::NotHidden,
  cl::desc("Set IR Indirect Branch Obfuscation Level."),
  cl::ZeroOrMore);


// 启用间接调用混淆的开关与级别设置
static cl::opt<bool>
EnableIndirectCall("irobf-icall", cl::init(false), cl::NotHidden,
                   cl::desc("Enable IR Indirect Call Obfuscation."),
                   cl::ZeroOrMore);
static cl::opt<uint32_t>
LevelIndirectCall("level-icall", cl::init(0), cl::NotHidden,
  cl::desc("Set IR Indirect Call Obfuscation Level."),
  cl::ZeroOrMore);


// 启用全局变量间接化的开关与级别设置
static cl::opt<bool> EnableIndirectGV(
    "irobf-indgv", cl::init(false), cl::NotHidden,
    cl::desc("Enable IR Indirect Global Variable Obfuscation."),
    cl::ZeroOrMore);
static cl::opt<uint32_t> LevelIndirectGV(
  "level-indgv", cl::init(0), cl::NotHidden,
  cl::desc("Set IR Indirect Global Variable Obfuscation Level."),
  cl::ZeroOrMore);


// 启用控制流平坦化（Control Flow Flattening）的开关
static cl::opt<bool> EnableIRFlattening(
    "irobf-cff", cl::init(false), cl::NotHidden,
    cl::desc("Enable IR Control Flow Flattening Obfuscation."), cl::ZeroOrMore);


// 启用常量字符串加密的开关
static cl::opt<bool>
EnableIRStringEncryption("irobf-cse", cl::init(false), cl::NotHidden,
                         cl::desc("Enable IR Constant String Encryption."),
                         cl::ZeroOrMore);


// 启用整型常量加密的开关与级别设置
static cl::opt<bool>
EnableIRConstantIntEncryption("irobf-cie", cl::init(false), cl::NotHidden,
  cl::desc("Enable IR Constant Integer Encryption."),
  cl::ZeroOrMore);
static cl::opt<uint32_t> LevelIRConstantIntEncryption(
  "level-cie", cl::init(0), cl::NotHidden,
  cl::desc("Set IR Constant Integer Encryption Level."),
  cl::ZeroOrMore);


// 启用浮点常量加密的开关与级别设置
static cl::opt<bool>
EnableIRConstantFPEncryption("irobf-cfe", cl::init(false), cl::NotHidden,
  cl::desc("Enable IR Constant FP Encryption."),
  cl::ZeroOrMore);

static cl::opt<uint32_t> LevelIRConstantFPEncryption(
  "level-cfe", cl::init(0), cl::NotHidden,
  cl::desc("Set IR Constant FP Encryption Level."),
  cl::ZeroOrMore);

namespace llvm {

/**
 * 混淆 Pass 管理器，用于集中管理多个混淆 Pass。
 */
struct ObfuscationPassManager : public ModulePass {
  static char            ID; // Pass identification
  // 存储所有混淆 Pass
  SmallVector<Pass *, 8> Passes;

  ObfuscationPassManager() : ModulePass(ID) {
    // 注册这个 Pass 到 LLVM PassManager 中
    initializeObfuscationPassManagerPass(*PassRegistry::getPassRegistry());
  };

  StringRef getPassName() const override {
    return "Obfuscation Pass Manager";
  }

  /**
   * 所有 Pass 的最终清理操作
   */
  bool doFinalization(Module &M) override {
    bool Change = false;
    for (Pass *P : Passes) {
      Change |= P->doFinalization(M);
      delete (P);
    }
    return Change;
  }

  void add(Pass *P) {
    Passes.push_back(P);
  }

  /**
   * 运行所有 Pass
   */
  bool run(Module &M) {
    bool Change = false;
    for (Pass *P : Passes) {
      switch (P->getPassKind()) {
      case PassKind::PT_Function:
        Change |= runFunctionPass(M, (FunctionPass *)P);
        break;
      case PassKind::PT_Module:
        Change |= runModulePass(M, (ModulePass *)P);
        break;
      default:
        continue;
      }
    }
    return Change;
  }

  /**
   * 对模块中的每个函数运行 FunctionPass
   */
  bool runFunctionPass(Module &M, FunctionPass *P) {
    bool Changed = false;
    for (Function &F : M) {
      Changed |= P->runOnFunction(F);
    }
    return Changed;
  }

  /**
   * 对模块运行 ModulePass
   */
  bool runModulePass(Module &M, ModulePass *P) {
    return P->runOnModule(M);
  }

  /**
   * 构建并返回混淆选项对象
   */
  static ObfuscationOptions *getOptions() {
    ObfuscationOptions *Options = new ObfuscationOptions{
        new ObfOpt{EnableIndirectBr, LevelIndirectBr, "indbr"},
        new ObfOpt{EnableIndirectCall, LevelIndirectCall, "icall"},
        new ObfOpt{EnableIndirectGV, LevelIndirectGV, "indgv"},
        new ObfOpt{EnableIRFlattening, 0, "fla"},
        new ObfOpt{EnableIRStringEncryption, 0, "cse"},
        new ObfOpt{EnableIRConstantIntEncryption, LevelIRConstantIntEncryption, "cie"},
        new ObfOpt{EnableIRConstantFPEncryption, LevelIRConstantFPEncryption, "cfe"}};
    return Options;
  }

  /**
   * 在模块上运行混淆 Pass
   */
  bool runOnModule(Module &M) override {

    // 如果启用了任何子项混淆，则自动启用主混淆开关
    if (EnableIndirectBr || EnableIndirectCall || EnableIndirectGV ||
        EnableIRFlattening || EnableIRStringEncryption ||
      EnableIRConstantIntEncryption || EnableIRConstantFPEncryption) {
      EnableIRObfuscation = true;
    }

    if (!EnableIRObfuscation) {
      return false;
    }

    std::unique_ptr<ObfuscationOptions> Options(getOptions());

    // 获取指针大小（用于某些 Pass 需要架构信息）
    unsigned pointerSize = M.getDataLayout().getTypeAllocSize(
        PointerType::getUnqual(M.getContext()));

    // 添加 整数常量加密
    add(llvm::createConstantIntEncryptionPass(Options.get()));
    // 添加 浮点常量加密
    add(llvm::createConstantFPEncryptionPass(Options.get()));

    // 添加字符串加密 Pass
    if (EnableIRStringEncryption || Options->cseOpt()->isEnabled()) {
      add(llvm::createStringEncryptionPass(Options.get()));
    }

    // 添加 过程相关控制流平坦混淆
    add(llvm::createFlatteningPass(pointerSize, Options.get()));

    // 添加间接跳转混淆 Pass
    add(llvm::createIndirectBranchPass(pointerSize, Options.get()));

    // 添加间接调用混淆 Pass
    add(llvm::createIndirectCallPass(pointerSize, Options.get()));

    // 添加全局变量间接化 Pass
    add(llvm::createIndirectGlobalVariablePass(pointerSize, Options.get()));

    // 实际运行所有添加的 Pass
    bool Changed = run(M);

    return Changed;
  }
};

} // namespace llvm

char ObfuscationPassManager::ID = 0;

// 创建混淆 Pass 管理器实例
ModulePass *llvm::createObfuscationPassManager() {
  return new ObfuscationPassManager();
}

// 注册这个 Pass 到 LLVM PassManager 中
INITIALIZE_PASS_BEGIN(ObfuscationPassManager, "irobf", "Enable IR Obfuscation",
                      false, false)
INITIALIZE_PASS_END(ObfuscationPassManager, "irobf", "Enable IR Obfuscation",
                      false, false)