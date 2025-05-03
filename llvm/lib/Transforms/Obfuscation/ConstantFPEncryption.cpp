#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/ConstantFPEncryption.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Utils/GlobalStatus.h"
#include "llvm/Transforms/IPO/Attributor.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/CryptoUtils.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <map>
#include <set>
#include <iostream>
#include <algorithm>
#include <atomic>

#define DEBUG_TYPE "constant-fp-encryption"

using namespace llvm;

namespace {

static std::atomic<long> CFPCount(0); // 初始化为0

/**
 * 浮点常量加密
 */
struct ConstantFPEncryption : public FunctionPass {
  const char *const TAG = "浮点常量加密";

  static char         ID;
  ObfuscationOptions *ArgsOptions;
  CryptoUtils         RandomEngine;

  // 构造函数，接收混淆选项参数
  ConstantFPEncryption(ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->ArgsOptions = argsOptions;
  }

  // 返回 Pass 名称用于调试和日志输出
  StringRef getPassName() const override {
    return {"ConstantFPEncryption"};
  }

  GlobalVariable *createGlobalVariable(Module *M, Constant *C) {
    auto GV = new GlobalVariable(*M, C->getType(), false,
                              GlobalValue::LinkageTypes::PrivateLinkage,
                              C);
    long newValue = CFPCount.fetch_add(1) + 1;
    std::string GVName = "obf_cfp_";
    GVName += newValue;
    GV->setName(GVName);
    return GV;
  }

  // 加密方式0：将浮点常量转为整数进行简单减法加密
  Value *createConstantFPEncrypt0(BasicBlock::iterator ip, ConstantFP *CFP) {
    const auto  Module = ip->getModule();
    auto &LLVMContent = Module->getContext();

    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    // 获取浮点类型的位宽（如 float=32, double=64）
    const auto FPWidth = CFP->getType()->getPrimitiveSizeInBits().
                              getFixedValue();


    // 生成一个与浮点位宽相同的随机整数作为密钥
    const auto Key = ConstantInt::get(
        IntegerType::get(LLVMContent, FPWidth),
        RandomEngine.get_uint64_t());

    // 将浮点常量按位转为整数类型
    const auto FPInt = ConstantExpr::getBitCast(CFP, Key->getType());

    // Enc = FPInt - Key
    const auto Enc = ConstantExpr::getSub(FPInt, Key);

    // 创建私有全局变量存储 Enc 并加入 compiler.used 防止被优化
    auto       GV = createGlobalVariable(Module, Enc);

    appendToCompilerUsed(*Module, {GV});
    // 插入加载指令并还原原始值 NewOpr = bitcast(Key + Load(GV))
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto Add = IRB.CreateAdd(Key, Load);
    const auto NewOpr = IRB.CreateBitCast(Add, CFP->getType());
    return NewOpr;
  }

  // 加密方式1：引入 XOR 混淆逻辑
  Value *createConstantFPEncrypt1(BasicBlock::iterator ip, ConstantFP *CFP) {
    const auto  Module = ip->getModule();
    auto &LLVMContent = Module->getContext();

    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    const auto FPWidth = CFP->getType()->getPrimitiveSizeInBits().
      getFixedValue();


    // 生成两个随机整数 Key 和 XorKey
    const auto Key = ConstantInt::get(
      IntegerType::get(LLVMContent, FPWidth),
      RandomEngine.get_uint64_t());

    const auto XorKey = ConstantInt::get(Key->getType(),
      RandomEngine.get_uint64_t());


    // 将浮点常量转换为整数形式
    const auto FPInt = ConstantExpr::getBitCast(CFP, Key->getType());

    // Enc = (FPInt - Key) ^ XorKey
    auto Enc = ConstantExpr::getSub(FPInt, Key);
    Enc = ConstantExpr::getXor(Enc, XorKey);

    // 创建全局变量存储 Enc 和 XorKey
    auto       GV = createGlobalVariable(Module, Enc);
    appendToCompilerUsed(*Module, {GV});

    auto GXorKey = createGlobalVariable(Module, XorKey);
    appendToCompilerUsed(*Module, {GXorKey});

    // 解密过程：
    // NewOpr = bitcast(Key + (Load(Enc) ^ Load(XorKey)))
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto LoadXor = IRB.CreateLoad(XorKey->getType(), GXorKey);
    const auto XorOpr = IRB.CreateXor(Load, LoadXor);
    const auto Add = IRB.CreateAdd(Key, XorOpr);
    const auto NewOpr = IRB.CreateBitCast(Add, CFP->getType());
    return NewOpr;
  }

  // 加密方式2：引入乘法与 XOR 的组合变换
  Value *createConstantFPEncrypt2(BasicBlock::iterator ip, ConstantFP *CFP) {
    const auto  Module = ip->getModule();
    auto &LLVMContent = Module->getContext();

    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    const auto FPWidth = CFP->getType()->getPrimitiveSizeInBits().
      getFixedValue();


    // 生成两个随机整数 Key 和 XorKey
    const auto Key = ConstantInt::get(
      IntegerType::get(LLVMContent, FPWidth),
      RandomEngine.get_uint64_t());

    const auto XorKey = ConstantInt::get(Key->getType(),
      RandomEngine.get_uint64_t());

    // MulXorKey = Key * XorKey
    const auto MulXorKey = ConstantExpr::getMul(Key, XorKey);

    // 转换浮点为整数
    const auto FPInt = ConstantExpr::getBitCast(CFP, Key->getType());

    // Enc = (FPInt - Key) ^ MulXorKey
    auto Enc = ConstantExpr::getSub(FPInt, Key);
    Enc = ConstantExpr::getXor(Enc, MulXorKey);

    // 创建全局变量存储 Enc 和 XorKey
    auto       GV = createGlobalVariable(Module, Enc);
    appendToCompilerUsed(*Module, {GV});

    auto GXorKey = createGlobalVariable(Module, XorKey);
    appendToCompilerUsed(*Module, {GXorKey});

    // 解密过程：
    // NewOpr = bitcast(Key + (Load(Enc) ^ (Key * Load(XorKey))))
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto LoadXor = IRB.CreateLoad(XorKey->getType(), GXorKey);
    const auto MulOpr = IRB.CreateMul(Key, LoadXor);
    const auto XorOpr = IRB.CreateXor(Load, MulOpr);
    const auto Add = IRB.CreateAdd(Key, XorOpr);
    const auto NewOpr = IRB.CreateBitCast(Add, CFP->getType());
    return NewOpr;
  }

  // 加密方式3：多步复杂变换
  Value *createConstantFPEncrypt3(BasicBlock::iterator ip, ConstantFP *CFP) {
    const auto  Module = ip->getModule();
    auto &LLVMContent = Module->getContext();

    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    const auto FPWidth = CFP->getType()->getPrimitiveSizeInBits().
      getFixedValue();


    // 生成两个随机整数 Key 和 XorKey
    const auto Key = ConstantInt::get(
      IntegerType::get(LLVMContent, FPWidth),
      RandomEngine.get_uint64_t());

    auto XorKey = ConstantInt::get(Key->getType(),
      RandomEngine.get_uint64_t());

    // MulXorKey = Key * XorKey
    const auto MulXorKey = ConstantExpr::getMul(Key, XorKey);

    // 转换浮点为整数
    const auto FPInt = ConstantExpr::getBitCast(CFP, Key->getType());

    // Enc = (FPInt - Key) ^ MulXorKey
    auto Enc = ConstantExpr::getSub(FPInt, Key);
    Enc = ConstantExpr::getXor(Enc, MulXorKey);

    // 对 XorKey 进行多重变换
    XorKey = ConstantExpr::getNeg(XorKey);
    XorKey = ConstantExpr::getXor(XorKey, Enc);
    XorKey = ConstantExpr::getNeg(XorKey);

    // 创建全局变量存储 Enc 和变换后的 XorKey
    auto       GV = createGlobalVariable(Module, Enc);
    appendToCompilerUsed(*Module, {GV});

    auto GXorKey = createGlobalVariable(Module, XorKey);
    appendToCompilerUsed(*Module, {GXorKey});

    // 解密过程：
    // FinalXor = -( -LoadXor ^ Load(Enc) )
    // MulOpr = Key * FinalXor
    // NewOpr = bitcast(Key + (Load(Enc) ^ MulOpr))
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto LoadXor = IRB.CreateLoad(XorKey->getType(), GXorKey);
    const auto XorKeyNegOpr = IRB.CreateNeg(LoadXor);
    const auto XorKeyXorEnc = IRB.CreateXor(XorKeyNegOpr, Load);
    const auto FinalXor = IRB.CreateNeg(XorKeyXorEnc);

    const auto MulOpr = IRB.CreateMul(Key, FinalXor);
    const auto XorOpr = IRB.CreateXor(Load, MulOpr);
    const auto Add = IRB.CreateAdd(Key, XorOpr);
    const auto NewOpr = IRB.CreateBitCast(Add, CFP->getType());
    return NewOpr;
  }

  // 主要执行函数，对函数中的浮点常量进行替换加密
  bool runOnFunction(Function &F) override {
    // 获取当前函数是否需要应用此 Pass 及其加密等级
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->cfeOpt(), &F);
    if (!opt.isEnabled()) {
      return false;
    }

    // 展开可能存在的 ConstantExpr（常量表达式）
    bool Changed = expandConstantExpr(F);

    // 遍历函数中的每个基本块和每条指令
    for (auto &BB : F) {
      for (auto &I : BB) {
        // 跳过异常处理指令、alloca、intrinsic、switch 和原子操作
        if (I.isEHPad() || isa<AllocaInst>(&I) || isa<IntrinsicInst>(&I) ||
            isa<SwitchInst>(&I) || I.isAtomic()) {
          continue;
        }

        // 获取当前指令的操作数插入点（对于 PHI Node 插入到入口块）
        auto CI = dyn_cast<CallInst>(&I);
        auto GEP = dyn_cast<GetElementPtrInst>(&I);
        auto IsPhi = isa<PHINode>(&I);
        auto InsertPt = IsPhi
                          ? F.getEntryBlock().getFirstInsertionPt()
                          : I.getIterator();

        // 遍历所有操作数，查找 ConstantFP 类型
        for (unsigned i = 0; i < I.getNumOperands(); ++i) {
          if (CI && CI->isBundleOperand(i)) {
            continue;
          }
          if (GEP && (i < 2 || GEP->getSourceElementType()->isStructTy())) {
            continue;
          }

          auto Opr = I.getOperand(i);
          if (auto CFP = dyn_cast<ConstantFP>(Opr)) {
            outs() << '[' << ConstantFPEncryption::TAG << "] " << I << " -> ";
//            I.print(outs());

            Value *NewOpr;

            // 根据加密等级选择不同的加密方法
            if (opt.level() == 0) {
              NewOpr = createConstantFPEncrypt0(InsertPt, CFP);
            } else if (opt.level() == 1) {
              NewOpr = createConstantFPEncrypt1(InsertPt, CFP);
            } else if (opt.level() == 2) {
              NewOpr = createConstantFPEncrypt2(InsertPt, CFP);
            } else {
              NewOpr = createConstantFPEncrypt3(InsertPt, CFP);
            }

            // 替换原操作数为加密后的表达式
            I.setOperand(i, NewOpr);
            outs() << I << "\n\n";
            Changed = true;
          }
        }

      }
    }
    return Changed;
  }
};
} // namespace llvm

// Pass ID 定义
char ConstantFPEncryption::ID = 0;

// 创建 ConstantFPEncryption 实例的工厂函数
FunctionPass *llvm::createConstantFPEncryptionPass(
    ObfuscationOptions *argsOptions) {
  return new ConstantFPEncryption(argsOptions);
}

// 注册该 Pass 到 LLVM PassManager 中
INITIALIZE_PASS(ConstantFPEncryption, "cfe",
                "Enable IR Constant FP Encryption", false, false)