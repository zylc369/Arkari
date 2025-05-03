#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Obfuscation/IndirectCall.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/Module.h"

#include <random>

#define DEBUG_TYPE "icall"

using namespace llvm;
namespace {
/**
 * 间接函数调用,并加密目标函数地址
 */
struct IndirectCall : public FunctionPass {
  static char ID;
  // 指针大小（4或8字节）
  unsigned pointerSize;
  
  // 混淆选项配置
  ObfuscationOptions *ArgsOptions;
  // 被调用函数到编号的映射
  std::map<Function *, unsigned> CalleeNumbering;
  // 所有调用点的列表
  std::vector<CallInst *> CallSites;
  // 所有被调用函数的列表
  std::vector<Function *> Callees;
  // 随机数生成器
  CryptoUtils RandomEngine;

  // 构造函数，初始化指针大小和混淆参数
  IndirectCall(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  // 返回 Pass 的名称
  StringRef getPassName() const override { return {"IndirectCall"}; }

  // 遍历函数中的所有指令，收集所有直接调用，并为每个被调用函数分配一个唯一编号
  void NumberCallees(Function &F) {
    for (auto &BB:F) {
      for (auto &I:BB) {
        if (dyn_cast<CallInst>(&I)) {
          CallBase *CB = dyn_cast<CallBase>(&I);
          Function *Callee = CB->getCalledFunction();
          if (Callee == nullptr) {
            // 忽略间接调用
            continue;
          }
          if (Callee->isIntrinsic()) {
            // 忽略 intrinsic 函数
            continue;
          }
          // 记录调用点
          CallSites.push_back((CallInst *) &I);
          if (CalleeNumbering.count(Callee) == 0) {
            // 初始化编号
            CalleeNumbering[Callee] = 0;
            // 添加新的被调用函数
            Callees.push_back(Callee);
          }
        }
      }
    }

    // 获取随机种子
    long seed = RandomEngine.get_uint32_t();
    // 初始化随机引擎
    std::default_random_engine e(seed);
    // 对被调用函数进行洗牌打乱顺序
    std::shuffle(Callees.begin(), Callees.end(), e);
    unsigned N = 0;
    for (auto Callee:Callees) {
      // 分配新编号
      CalleeNumbering[Callee] = N++;
    }
  }

  // 创建全局变量，用于存储加密后的函数地址（模式0：仅使用加法密钥）
  GlobalVariable *getIndirectCallees0(Function &F, ConstantInt *EncKey) const {
    std::string GVName(F.getName().str() + "_IndirectCallees");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    // 构建加密后的函数地址数组
    // callee's address
    std::vector<Constant *> Elements;
    for (auto Callee:Callees) {
      Constant *CE = ConstantExpr::getBitCast(
          Callee, PointerType::getUnqual(F.getContext()));
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

  // 创建全局变量，用于存储加密后的函数地址（模式1：使用异或密钥）
  GlobalVariable *getIndirectCallees1(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) const {
    std::string GVName(F.getName().str() + "_IndirectCallees1");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    // 构建加密后的函数地址数组
    // callee's address
    std::vector<Constant *> Elements;
    for (auto Callee:Callees) {
      Constant *CE = ConstantExpr::getBitCast(
        Callee, PointerType::getUnqual(F.getContext()));
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

  // 创建全局变量，用于存储加密后的函数地址（模式2：基于编号的乘法+异或加密）
  GlobalVariable * getIndirectCallees2(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) {
    std::string GVName(F.getName().str() + "_IndirectCallees2");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;


    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    // 构建加密后的函数地址数组
    // callee's address
    std::vector<Constant *> Elements;
    for (auto Callee:Callees) {
      Constant *CE = ConstantExpr::getBitCast(
        Callee, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, CalleeNumbering[Callee], false))));
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

  // 创建两个全局变量，分别存储加法和异或密钥（模式3：更复杂的动态密钥机制）
  std::pair<GlobalVariable *, GlobalVariable *> getIndirectCallees3(Function &F, ConstantInt *AddKey) {
    std::string GVNameAdd(F.getName().str() + "_IndirectCallees3_Add");
    std::string GVNameXor(F.getName().str() + "_IndirectCallees3_Xor");
    GlobalVariable *GVAdd = F.getParent()->getNamedGlobal(GVNameAdd);
    GlobalVariable *GVXor = F.getParent()->getNamedGlobal(GVNameXor);
    if (GVAdd && GVXor)
      return std::make_pair(GVAdd, GVXor);


    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    // 构建加密后的函数地址数组以及对应的异或密钥数组
    // callee's address
    std::vector<Constant *> Elements;
    std::vector<Constant *> XorKeys;
    for (auto Callee:Callees) {
      uint64_t V = RandomEngine.get_uint64_t();
      Constant *XorKey = ConstantInt::get(intType, V, false);

      Constant *CE = ConstantExpr::getBitCast(
        Callee, PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, CalleeNumbering[Callee], false))));

      XorKey = ConstantExpr::getNeg(XorKey);
      XorKey = ConstantExpr::getXor(XorKey, AddKey);
      XorKey = ConstantExpr::getNeg(XorKey);
      XorKeys.push_back(XorKey);
      Elements.push_back(CE);
    }

    ArrayType *ATy =
      ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));
    GVAdd = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
      CA, GVNameAdd);
    appendToCompilerUsed(*F.getParent(), {GVAdd});

    ArrayType *XTy = ArrayType::get(intType, XorKeys.size());
    Constant *CX = ConstantArray::get(XTy, XorKeys);
    GVXor = new GlobalVariable(*F.getParent(), XTy, false, GlobalValue::LinkageTypes::PrivateLinkage, CX, GVNameXor);
    appendToCompilerUsed(*F.getParent(), {GVXor});

    return std::make_pair(GVAdd, GVXor);
  }

  // 主要处理函数，执行间接调用转换
  bool runOnFunction(Function &Fn) override {
    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->iCallOpt(), &Fn);
    if (!opt.isEnabled()) {
      // 如果禁用该优化，则直接返回
      return false;
    }

    LLVMContext &Ctx = Fn.getContext();

    CalleeNumbering.clear();
    Callees.clear();
    CallSites.clear();

    // 收集并编号所有被调用函数
    NumberCallees(Fn);

    if (Callees.empty()) {
      // 如果没有可替换的调用点，退出
      return false;
    }

    // 加密密钥
    uint64_t V = RandomEngine.get_uint64_t();
    // 异或密钥
    uint64_t XV = RandomEngine.get_uint64_t();

    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }
    ConstantInt *EncKey = ConstantInt::get(intType, V, false);
    ConstantInt *EncKey1 = ConstantInt::get(intType, -V, false);
    ConstantInt *Zero = ConstantInt::get(intType, 0);

    GlobalVariable *GXorKey = nullptr;
    GlobalVariable *Targets = nullptr;
    GlobalVariable *XorKeys = nullptr;

    // 根据混淆等级选择不同的加密方式
    if (opt.level() == 0) {
      Targets = getIndirectCallees0(Fn, EncKey1);
    } else if (opt.level() == 1 || opt.level() == 2) {
      ConstantInt *CXK = ConstantInt::get(intType, XV, false);
      GXorKey = new GlobalVariable(*Fn.getParent(), CXK->getType(), false, GlobalValue::LinkageTypes::PrivateLinkage,
        CXK, Fn.getName() + "_ICallXorKey");
      appendToCompilerUsed(*Fn.getParent(), {GXorKey});

      if (opt.level() == 1) {
        Targets = getIndirectCallees1(Fn, EncKey1, CXK);
      } else {
        Targets = getIndirectCallees2(Fn, EncKey1, CXK);
      }
    } else {
      auto [fst, snd] = getIndirectCallees3(Fn, EncKey1);
      Targets = fst;
      XorKeys = snd;
    }

    // 替换所有调用点为间接调用
    for (auto CI : CallSites) {

      CallBase *CB = CI;

      Function *Callee = CB->getCalledFunction();
      FunctionType *FTy = Callee->getFunctionType();
      IRBuilder<> IRB(CB);

      Value *Idx = ConstantInt::get(intType, CalleeNumbering[CB->getCalledFunction()]);
      Value *GEP = IRB.CreateGEP(
          Targets->getValueType(), Targets,
          {Zero, Idx});
      Value *EncDestAddr = IRB.CreateLoad(
          GEP->getType(), GEP,
          CI->getName());

      Value *DecKey = EncKey;

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

      if (XorKeys) {
        Value *XorKeysGEP = IRB.CreateGEP(XorKeys->getValueType(), XorKeys, {Zero, Idx});
        
        Value *XorKey = IRB.CreateLoad(intType, XorKeysGEP);

        XorKey = IRB.CreateNeg(XorKey);
        XorKey = IRB.CreateXor(XorKey, EncKey1);
        XorKey = IRB.CreateNeg(XorKey);

        DecKey = IRB.CreateXor(EncKey1, IRB.CreateMul(XorKey, Idx));
        DecKey = IRB.CreateNeg(DecKey);
      }

      // 解密目标地址
      Value *DestAddr = IRB.CreateGEP(Type::getInt8Ty(Ctx),
          EncDestAddr, DecKey);

      // 将解密后的地址转换为函数指针
      Value *FnPtr = IRB.CreateBitCast(DestAddr, FTy->getPointerTo());
      FnPtr->setName("Call_" + Callee->getName());

      // 替换调用操作数为目标函数指针
      CB->setCalledOperand(FnPtr);
    }

    return true;
  }

};
} // namespace llvm

char IndirectCall::ID = 0;
FunctionPass *llvm::createIndirectCallPass(unsigned pointerSize, ObfuscationOptions *argsOptions) {
  return new IndirectCall(pointerSize, argsOptions);
}

INITIALIZE_PASS(IndirectCall, "icall", "Enable IR Indirect Call Obfuscation", false, false)
