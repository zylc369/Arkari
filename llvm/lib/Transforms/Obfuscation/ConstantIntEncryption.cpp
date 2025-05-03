#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/ConstantIntEncryption.h"
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

#define DEBUG_TYPE "constant-int-encryption"

using namespace llvm;

namespace {

static std::atomic<long> CICount(0); // 初始化为0

/**
 * 整数常量加密
 */
struct ConstantIntEncryption : public FunctionPass {
  static char         ID;
  ObfuscationOptions *ArgsOptions;
  CryptoUtils         RandomEngine;

  // 构造函数，接受混淆选项参数
  ConstantIntEncryption(ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->ArgsOptions = argsOptions;
  }

  GlobalVariable *createGlobalVariable(Module *M, Constant *C) {
      auto GV = new GlobalVariable(*M, C->getType(), false,
                              GlobalValue::LinkageTypes::PrivateLinkage,
                              C);
      long newValue = CICount.fetch_add(1) + 1;
      std::string GVName = "obf_ci_";
      GVName += newValue;
      GV->setName(GVName);
      return GV;
  }

  // 加密方式0：使用简单的加法/减法加密常量整数
  Value *createConstantIntEncrypt0(BasicBlock::iterator ip, ConstantInt *CIT) {
    const auto          Module = ip->getModule();
    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    // 生成一个随机密钥用于加密
    const auto Key = ConstantInt::get(CIT->getType(),
                                      RandomEngine.get_uint64_t());

    // 计算加密后的值 Enc = CIT - Key
    const auto Enc = ConstantExpr::getSub(CIT, Key);

    // 创建一个私有全局变量存储 Enc，并加入 compiler.used 列表防止被优化掉
    auto       GV = createGlobalVariable(Module, Enc);
    appendToCompilerUsed(*Module, {GV});
    // 创建加载指令 Load(GV)，然后计算 NewOpr = Key + Load(GV)
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto NewOpr = IRB.CreateAdd(Key, Load);
    return NewOpr;
  }

  // 加密方式1：引入 XOR 混淆逻辑
  Value *createConstantIntEncrypt1(BasicBlock::iterator ip, ConstantInt *CIT) {
    const auto          Module = ip->getModule();
    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    // 生成两个随机密钥 Key 和 XorKey
    const auto Key = ConstantInt::get(CIT->getType(),
                                      RandomEngine.get_uint64_t());
    const auto XorKey = ConstantInt::get(CIT->getType(),
                                         RandomEngine.get_uint64_t());

    // Enc = (CIT - Key) ^ XorKey
    auto Enc = ConstantExpr::getSub(CIT, Key);
    Enc = ConstantExpr::getXor(Enc, XorKey);

    // 存储 Enc 和 XorKey 到全局变量并加入 compiler.used
    auto GV = createGlobalVariable(Module, Enc);
    appendToCompilerUsed(*Module, {GV});

    auto GXorKey = createGlobalVariable(Module, XorKey);
    appendToCompilerUsed(*Module, {GXorKey});

    // 解密过程：NewOpr = Key + ((Load(Enc) ^ Load(XorKey)))
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto LoadXor = IRB.CreateLoad(XorKey->getType(), GXorKey);
    const auto XorOpr = IRB.CreateXor(Load, LoadXor);
    const auto NewOpr = IRB.CreateAdd(Key, XorOpr);
    return NewOpr;
  }

  // 加密方式2：引入乘法和 XOR 的组合
  Value *createConstantIntEncrypt2(BasicBlock::iterator ip, ConstantInt *CIT) {
    const auto          Module = ip->getModule();
    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    // 生成两个随机密钥 Key 和 XorKey
    const auto Key = ConstantInt::get(CIT->getType(),
                                      RandomEngine.get_uint64_t());
    const auto XorKey = ConstantInt::get(CIT->getType(),
                                         RandomEngine.get_uint64_t());

    // MulXorKey = Key * XorKey
    const auto MulXorKey = ConstantExpr::getMul(Key, XorKey);

    // Enc = (CIT - Key) ^ MulXorKey
    auto Enc = ConstantExpr::getSub(CIT, Key);
    Enc = ConstantExpr::getXor(Enc, MulXorKey);

    // 将 Enc 和 XorKey 放入全局变量中
    auto GV = createGlobalVariable(Module, Enc);
    appendToCompilerUsed(*Module, {GV});

    auto GXorKey = createGlobalVariable(Module, XorKey);
    appendToCompilerUsed(*Module, {GXorKey});

    // 解密过程：
    // NewOpr = Key + ((Load(Enc) ^ (Key * Load(XorKey))))
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto LoadXor = IRB.CreateLoad(XorKey->getType(), GXorKey);
    const auto MulOpr = IRB.CreateMul(Key, LoadXor);
    const auto XorOpr = IRB.CreateXor(Load, MulOpr);
    const auto NewOpr = IRB.CreateAdd(Key, XorOpr);
    return NewOpr;
  }

  // 加密方式3：更复杂的多步变换逻辑
  Value *createConstantIntEncrypt3(BasicBlock::iterator ip, ConstantInt *CIT) {
    const auto          Module = ip->getModule();
    IRBuilder<NoFolder> IRB(ip->getContext());
    IRB.SetInsertPoint(ip);

    // 生成两个随机密钥 Key 和 XorKey
    const auto Key = ConstantInt::get(CIT->getType(),
                                      RandomEngine.get_uint64_t());
    auto XorKey = ConstantInt::get(CIT->getType(),
                                         RandomEngine.get_uint64_t());

    // MulXorKey = Key * XorKey
    const auto MulXorKey = ConstantExpr::getMul(Key, XorKey);

    // Enc = (CIT - Key) ^ MulXorKey
    auto Enc = ConstantExpr::getSub(CIT, Key);
    Enc = ConstantExpr::getXor(Enc, MulXorKey);

    // 对 XorKey 做多重变换后存入全局变量
    XorKey = ConstantExpr::getNeg(XorKey);
    XorKey = ConstantExpr::getXor(XorKey, Enc);
    XorKey = ConstantExpr::getNeg(XorKey);

    // 创建全局变量存储 Enc 和变换后的 XorKey
    auto GV = createGlobalVariable(Module, Enc);
    appendToCompilerUsed(*Module, {GV});

    auto GXorKey = createGlobalVariable(Module, XorKey);
    appendToCompilerUsed(*Module, {GXorKey});

    // 解密过程：
    // FinalXor = -( -LoadXor ^ Load(Enc) )
    // MulOpr = Key * FinalXor
    // NewOpr = Key + (Load(Enc) ^ MulOpr)
    // outs() << I << " ->\n";
    const auto Load = IRB.CreateLoad(Enc->getType(), GV);
    const auto LoadXor = IRB.CreateLoad(XorKey->getType(), GXorKey);
    const auto XorKeyNegOpr = IRB.CreateNeg(LoadXor);
    const auto XorKeyXorEnc = IRB.CreateXor(XorKeyNegOpr, Load);
    const auto FinalXor = IRB.CreateNeg(XorKeyXorEnc);

    const auto MulOpr = IRB.CreateMul(Key, FinalXor);
    const auto XorOpr = IRB.CreateXor(Load, MulOpr);
    const auto NewOpr = IRB.CreateAdd(Key, XorOpr);
    return NewOpr;
  }

  // 主要执行函数，对函数中的常量整数进行替换加密
  bool runOnFunction(Function &F) override {
    // 获取当前函数是否需要应用此 Pass 及其加密等级
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->cieOpt(), &F);
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

        // 遍历所有操作数，查找 ConstantInt 类型
        for (unsigned i = 0; i < I.getNumOperands(); ++i) {
          if (CI && CI->isBundleOperand(i)) {
            continue;
          }
          if (GEP && (i < 2 || GEP->getSourceElementType()->isStructTy())) {
            continue;
          }
          auto Opr = I.getOperand(i);
          if (auto CIT = dyn_cast<ConstantInt>(Opr)) {
            Value *NewOpr;
            // 根据加密等级选择不同的加密方法
            if (opt.level() == 0) {
              NewOpr = createConstantIntEncrypt0(InsertPt, CIT);
            } else if (opt.level() == 1) {
              NewOpr = createConstantIntEncrypt1(InsertPt, CIT);
            } else if (opt.level() == 2) {
              NewOpr = createConstantIntEncrypt2(InsertPt, CIT);
            } else {
              NewOpr = createConstantIntEncrypt3(InsertPt, CIT);
            }

            // 替换原操作数为加密后的表达式
            I.setOperand(i, NewOpr);
            // outs() << I << "\n\n";
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
char ConstantIntEncryption::ID = 0;

// 创建 ConstantIntEncryption 实例的工厂函数
FunctionPass *llvm::createConstantIntEncryptionPass(
    ObfuscationOptions *argsOptions) {
  return new ConstantIntEncryption(argsOptions);
}

// 注册该 Pass 到 LLVM PassManager 中
INITIALIZE_PASS(ConstantIntEncryption, "cie",
                "Enable IR Constant Integer Encryption", false, false)