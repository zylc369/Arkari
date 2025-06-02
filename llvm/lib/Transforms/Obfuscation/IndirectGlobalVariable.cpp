#include "llvm/Transforms/Obfuscation/IndirectGlobalVariable.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include <random>

#define DEBUG_TYPE "indgv"

using namespace llvm;
namespace {
/**
 * 间接全局变量引用,并加密变量地址
 */
struct IndirectGlobalVariable : public FunctionPass {
  // 当前架构指针大小（32位或64位）
  unsigned pointerSize;
  // Pass 唯一标识符
  static char ID;
  
  // 混淆选项参数，控制混淆行为
  ObfuscationOptions *ArgsOptions;
  // 全局变量编号映射
  std::map<GlobalVariable *, unsigned> GVNumbering;
  // 所有被引用的全局变量列表
  std::vector<GlobalVariable *> GlobalVariables;
  // 加密用随机数生成器
  CryptoUtils RandomEngine;

  // 构造函数，初始化指针大小与混淆选项
  IndirectGlobalVariable(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  // 返回 Pass 名称
  StringRef getPassName() const override { return {"IndirectGlobalVariable"}; }

  // 遍历函数中的指令，找出所有直接使用的全局变量，并进行编号
  void NumberGlobalVariable(Function &F) {
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      for (User::op_iterator op = (*I).op_begin(); op != (*I).op_end(); ++op) {
        Value *val = *op;
        if (GlobalVariable *GV = dyn_cast<GlobalVariable>(val)) {
          // 过滤线程局部变量、DLL 导入依赖项，并确保每个全局变量只处理一次
          if (!GV->isThreadLocal() && GVNumbering.count(GV) == 0 &&
              !GV->isDLLImportDependent()) {
            GVNumbering[GV] = 0;
            GlobalVariables.push_back((GlobalVariable *) val);
          }
        }
      }
    }

    // 使用随机种子打乱全局变量顺序
    long seed = RandomEngine.get_uint32_t();
    std::default_random_engine e(seed);
    std::shuffle(GlobalVariables.begin(), GlobalVariables.end(), e);

    // 为每个变量分配唯一编号
    unsigned N = 0;
    for (auto GV:GlobalVariables) {
      GVNumbering[GV] = N++;
    }
  }

  // 创建一个加密后的全局变量数组，使用单一加密偏移量 EncKey
  GlobalVariable *getIndirectGlobalVariables0(Function &F, ConstantInt *EncKey) const {
    std::string GVName(F.getName().str() + "_IndirectGVars");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    std::vector<Constant *> Elements;
    for (auto GVar:GlobalVariables) {
      // 将全局变量转换为指针类型并加上 EncKey 偏移
      Constant *CE = ConstantExpr::getBitCast(
          GVar, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, EncKey);
      Elements.push_back(CE);
    }

    ArrayType *ATy =
        ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));
    GV = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
                            CA, GVName);
    appendToCompilerUsed(*F.getParent(), {GV});
    return GV;
  }

  // 使用 AddKey ^ XorKey 的结果作为偏移创建间接表
  GlobalVariable *getIndirectGlobalVariables1(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) const {
    std::string GVName(F.getName().str() + "_IndirectGVars1");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    std::vector<Constant *> Elements;
    for (auto GVar:GlobalVariables) {
      Constant *CE = ConstantExpr::getBitCast(
        GVar, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, XorKey));
      Elements.push_back(CE);
    }

    ArrayType *ATy =
      ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));
    GV = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
      CA, GVName);
    appendToCompilerUsed(*F.getParent(), {GV});
    return GV;
  }

  // 使用 AddKey ^ (XorKey * 编号) 作为偏移创建间接表
  GlobalVariable *getIndirectGlobalVariables2(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) {
    std::string GVName(F.getName().str() + "_IndirectGVars2");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      // 根据指针大小选择整型长度
      intType = Type::getInt64Ty(Ctx);
    }

    std::vector<Constant *> Elements;
    for (auto GVar:GlobalVariables) {
      Constant *CE = ConstantExpr::getBitCast(
        GVar, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, GVNumbering[GVar], false))));
      Elements.push_back(CE);
    }

    ArrayType *ATy =
      ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));
    GV = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
      CA, GVName);
    appendToCompilerUsed(*F.getParent(), {GV});
    return GV;
  }

  // 创建两个全局变量：一个包含加法偏移地址，另一个包含对应的 XOR 解密密钥
  std::pair<GlobalVariable *, GlobalVariable *> getIndirectGlobalVariables3(Function &F, ConstantInt *AddKey) {
    std::string GVNameAdd(F.getName().str() + "_IndirectGVars3");
    std::string GVNameXor(F.getName().str() + "_IndirectGVars3Xor");
    GlobalVariable *GVAdd = F.getParent()->getNamedGlobal(GVNameAdd);
    GlobalVariable *GVXor = F.getParent()->getNamedGlobal(GVNameXor);
    if (GVAdd && GVXor)
      return std::make_pair(GVAdd, GVXor);

    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      // 根据指针大小选择整型长度
      intType = Type::getInt64Ty(Ctx);
    }

    std::vector<Constant *> Elements;
    std::vector<Constant *> XorKeys;
    for (auto GVar:GlobalVariables) {
      uint64_t V = RandomEngine.get_uint64_t();
      // 为每个变量生成一个随机 XOR 密钥
      Constant *XorKey = ConstantInt::get(intType, V, false);

      Constant *CE = ConstantExpr::getBitCast(
        GVar, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, GVNumbering[GVar], false))));
      Elements.push_back(CE);

      // 计算用于解密的 XOR 密钥
      XorKey = ConstantExpr::getNeg(XorKey);
      XorKey = ConstantExpr::getXor(XorKey, AddKey);
      XorKey = ConstantExpr::getNeg(XorKey);
      XorKeys.push_back(XorKey);
    }

    // 创建地址表
    ArrayType *ATy =
      ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));
    GVAdd = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
      CA, GVNameAdd);
    appendToCompilerUsed(*F.getParent(), {GVAdd});

    // 创建 XOR 密钥表
    ArrayType *XTy = ArrayType::get(intType, XorKeys.size());
    Constant *CX = ConstantArray::get(XTy, XorKeys);
    GVXor = new GlobalVariable(*F.getParent(), XTy, false, GlobalValue::LinkageTypes::PrivateLinkage, CX, GVNameXor);
    appendToCompilerUsed(*F.getParent(), {GVXor});
    return std::make_pair(GVAdd, GVXor);
  }

  bool runOnFunction(Function &Fn) override {
    // 判断是否对当前函数启用全局变量间接化混淆
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->indGvOpt(), &Fn);
    if (!opt.isEnabled()) {
      return false;
    }

    LLVMContext &Ctx = Fn.getContext();

    // 清空之前的全局变量编号与列表
    GVNumbering.clear();
    GlobalVariables.clear();

    // 对常量表达式进行降级处理（例如 ConstantExpr 转为指令），便于后续分析
    LowerConstantExpr(Fn);

    // 收集函数中使用的所有全局变量并随机打乱顺序、分配唯一编号
    NumberGlobalVariable(Fn);

    // 如果没有需要混淆的全局变量，则跳过
    if (GlobalVariables.empty()) {
      return false;
    }

    // 生成两个随机密钥用于地址加密
    uint64_t V = RandomEngine.get_uint64_t();
    uint64_t XV = RandomEngine.get_uint64_t();

    // 根据指针大小选择整型类型（32位或64位）
    IntegerType* intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    // 创建几个用于加密的常量值：
    // EncKey: 正向偏移密钥；EncKey1: 负向偏移密钥；Zero: 索引0常量
    ConstantInt *EncKey = ConstantInt::get(intType, V, false);
    ConstantInt *EncKey1 = ConstantInt::get(intType, -V, false);
    ConstantInt *Zero = ConstantInt::get(intType, 0);

    // 声明用于存储间接表和解密信息的全局变量
    GlobalVariable *GXorKey = nullptr;
    GlobalVariable *GVars = nullptr;
    GlobalVariable *XorKeys = nullptr;

    // 根据混淆等级选择不同的加密策略
    if (opt.level() == 0) {
      // Level 0: 使用单一偏移量 EncKey1 加密地址
      GVars = getIndirectGlobalVariables0(Fn, EncKey1);
    } else if (opt.level() == 1 || opt.level() == 2) {
      // Level 1/2: 引入 XOR 密钥 CXK，结合编号进一步混淆
      ConstantInt *CXK = ConstantInt::get(intType, XV, false);
      GXorKey = new GlobalVariable(*Fn.getParent(), CXK->getType(), false, GlobalValue::LinkageTypes::PrivateLinkage,
        CXK, Fn.getName() + "_IGVXorKey");
      appendToCompilerUsed(*Fn.getParent(), {GXorKey});

      if (opt.level() == 1) {
        // Level 1: 使用 EncKey1 ^ CXK 的方式创建间接表
        GVars = getIndirectGlobalVariables1(Fn, EncKey1, CXK);
      } else {
        // Level 2: 使用 EncKey1 ^ (CXK * 编号) 的方式创建间接表
        GVars = getIndirectGlobalVariables2(Fn, EncKey1, CXK);
      }
    } else {
      // Level >=3: 使用双密钥方案，一个保存地址偏移，另一个保存对应的解密密钥
      auto [fst, snd] = getIndirectGlobalVariables3(Fn, EncKey1);
      GVars = fst;
      XorKeys = snd;
    }

    // 遍历函数中的每条指令，替换直接引用的全局变量为间接访问形式
    for (inst_iterator I = inst_begin(Fn), E = inst_end(Fn); I != E; ++I) {
      Instruction *Inst = &*I;

      // 忽略异常处理相关指令和 Call 指令
      if (isa<LandingPadInst>(Inst) || isa<CleanupPadInst>(Inst) ||
          isa<CatchPadInst>(Inst) || isa<CatchReturnInst>(Inst) ||
          isa<CatchSwitchInst>(Inst) || isa<ResumeInst>(Inst) || 
          isa<CallInst>(Inst)) {
        continue;
      }

      // 处理 PHI 节点的 incoming value
      if (PHINode *PHI = dyn_cast<PHINode>(Inst)) {
        for (unsigned int i = 0; i < PHI->getNumIncomingValues(); ++i) {
          Value *val = PHI->getIncomingValue(i);
          if (GlobalVariable *GV = dyn_cast<GlobalVariable>(val)) {
            if (GVNumbering.count(GV) == 0) {
              // 只处理被编号过的全局变量
              continue;
            }

            // 在该 incoming block 的 terminator 前插入间接加载逻辑
            Instruction *IP = PHI->getIncomingBlock(i)->getTerminator();
            IRBuilder<> IRB(IP);

            // 获取索引
            Value *Idx = ConstantInt::get(intType, GVNumbering[GV]);

            // 创建 GEP 指向间接表项
            Value *GEP = IRB.CreateGEP(
                GVars->getValueType(),
                GVars,
                {Zero, Idx});

            // 从间接表中加载混淆后的地址
            LoadInst *EncGVAddr = IRB.CreateLoad(
                GEP->getType(), GEP,
                GV->getName());

            // 初始化解密密钥
            Value *DecKey = EncKey;

            // 如果使用了 XOR 密钥（level 1 或 2），则动态计算解密偏移
            if (GXorKey) {
              LoadInst *XorKey = IRB.CreateLoad(GXorKey->getValueType(), GXorKey);

              if (opt.level() == 1) {
                DecKey = IRB.CreateXor(EncKey1, XorKey);
                DecKey = IRB.CreateNeg(DecKey);
              } else if (opt.level() == 2) {
                DecKey = IRB.CreateXor(EncKey1, IRB.CreateMul(XorKey, Idx));
                DecKey = IRB.CreateNeg(DecKey);
              }
            }

            // 如果是 level >=3，使用双密钥方案进行解密
            if (XorKeys) {
              Value *XorKeysGEP = IRB.CreateGEP(XorKeys->getValueType(), XorKeys, {Zero, Idx});

              Value *XorKey = IRB.CreateLoad(intType, XorKeysGEP);

              XorKey = IRB.CreateNeg(XorKey);
              XorKey = IRB.CreateXor(XorKey, EncKey1);
              XorKey = IRB.CreateNeg(XorKey);

              DecKey = IRB.CreateXor(EncKey1, IRB.CreateMul(XorKey, Idx));
              DecKey = IRB.CreateNeg(DecKey);
            }

            // 解密后还原真实地址，并做 BitCast 类型转换
            Value *GVAddr = IRB.CreateGEP(
              Type::getInt8Ty(Ctx),
                EncGVAddr,
              DecKey);
            GVAddr = IRB.CreateBitCast(GVAddr, GV->getType());
            GVAddr->setName("IndGV0_");

            // 替换 PHI 节点中的 incoming value 为间接地址
            PHI->setIncomingValue(i, GVAddr);
          }
        }
      } else {
        // 处理普通指令的操作数
        for (User::op_iterator op = Inst->op_begin(); op != Inst->op_end(); ++op) {
          if (GlobalVariable *GV = dyn_cast<GlobalVariable>(*op)) {
            if (GVNumbering.count(GV) == 0) {
              // 只处理被编号过的全局变量
              continue;
            }

            IRBuilder<> IRB(Inst);

            // 获取索引
            Value *Idx = ConstantInt::get(intType, GVNumbering[GV]);

            // 创建 GEP 指向间接表项
            Value *GEP = IRB.CreateGEP(
                GVars->getValueType(),
                GVars,
                {Zero, Idx});

            // 从间接表中加载混淆后的地址
            LoadInst *EncGVAddr = IRB.CreateLoad(
                GEP->getType(),
                GEP,
                GV->getName());

            // 初始化解密密钥
            Value *DecKey = EncKey;

            // 如果使用了 XOR 密钥（level 1 或 2），则动态计算解密偏移
            if (GXorKey) {
              LoadInst *XorKey = IRB.CreateLoad(GXorKey->getValueType(), GXorKey);

              if (opt.level() == 1) {
                DecKey = IRB.CreateXor(EncKey1, XorKey);
                DecKey = IRB.CreateNeg(DecKey);
              } else if (opt.level() == 2) {
                DecKey = IRB.CreateXor(EncKey1, IRB.CreateMul(XorKey, Idx));
                DecKey = IRB.CreateNeg(DecKey);
              }
            }

            // 如果是 level >=3，使用双密钥方案进行解密
            if (XorKeys) {
              Value *XorKeysGEP = IRB.CreateGEP(XorKeys->getValueType(), XorKeys, {Zero, Idx});

              Value *XorKey = IRB.CreateLoad(intType, XorKeysGEP);

              XorKey = IRB.CreateNeg(XorKey);
              XorKey = IRB.CreateXor(XorKey, EncKey1);
              XorKey = IRB.CreateNeg(XorKey);

              DecKey = IRB.CreateXor(EncKey1, IRB.CreateMul(XorKey, Idx));
              DecKey = IRB.CreateNeg(DecKey);
            }

            // 解密后还原真实地址，并做 BitCast 类型转换
            Value *GVAddr = IRB.CreateGEP(
              Type::getInt8Ty(Ctx),
                EncGVAddr,
                DecKey);
            GVAddr = IRB.CreateBitCast(GVAddr, GV->getType());
            GVAddr->setName("IndGV1_");

            // 替换原指令中对该全局变量的直接引用
            Inst->replaceUsesOfWith(GV, GVAddr);
          }
        }
      }
    }

    // 表示本 Pass 对函数进行了修改
      return true;
    }

  };
} // namespace llvm

char IndirectGlobalVariable::ID = 0;
FunctionPass *llvm::createIndirectGlobalVariablePass(unsigned pointerSize, ObfuscationOptions *argsOptions) {
  return new IndirectGlobalVariable(pointerSize, argsOptions);
}

INITIALIZE_PASS(IndirectGlobalVariable, "indgv", "Enable IR Indirect Global Variable Obfuscation", false, false)
