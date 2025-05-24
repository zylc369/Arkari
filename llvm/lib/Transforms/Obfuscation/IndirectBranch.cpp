#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Obfuscation/IndirectBranch.h"
#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/Module.h"

#include <random>

#define DEBUG_TYPE "indbr"

using namespace llvm;
namespace {
/**
 * 间接跳转，并加密跳转目标
 */
struct IndirectBranch : public FunctionPass {
  const char * const TAG = "间接跳转，并加密跳转目标";

  // 当前平台指针大小（4 或 8 字节）
  unsigned pointerSize;
  static char ID;

  // 混淆选项配置
  ObfuscationOptions *ArgsOptions;
  // 基本块编号映射
  std::map<BasicBlock *, unsigned> BBNumbering;
  // 所有条件跳转的目标基本块
  std::vector<BasicBlock *> BBTargets;        //all conditional branch targets
  // 加密随机数生成器
  CryptoUtils RandomEngine;

  // 构造函数：初始化指针大小和混淆选项
  IndirectBranch(unsigned pointerSize, ObfuscationOptions *argsOptions) : FunctionPass(ID) {
    this->pointerSize = pointerSize;
    this->ArgsOptions = argsOptions;
  }

  // 返回该 Pass 的名称
  StringRef getPassName() const override { return {"IndirectBranch"}; }

  // 遍历函数中的所有基本块，识别条件分支，并收集目标基本块
  void NumberBasicBlock(Function &F) {
    outs() << "[" << TAG << "] " << F.getName() << "\n\n";

    // 遍历函数 F 的所有基本块 BB（BasicBlock 类型）。
    for (auto &BB : F) {
      // BB.getTerminator() 获取基本块的终止指令（通常是分支、返回等）。
      // dyn_cast<BranchInst> 尝试转换为分支指令 BranchInst（失败则跳过）。
      if (auto *BI = dyn_cast<BranchInst>(BB.getTerminator())) {

        // BI->isConditional() 判断是否为条件分支（如 br i1 %cond, label %true, label %false）。
        if (BI->isConditional()) {
          // 获取后继块：BI->getNumSuccessors() 获取分支目标数量（条件分支通常为 2 个）。
          unsigned N = BI->getNumSuccessors();
          for (unsigned I = 0; I < N; I++) {
            BasicBlock *Succ = BI->getSuccessor(I);
            if (BBNumbering.count(Succ) == 0) {
              // 收集目标基本块
              BBTargets.push_back(Succ);
              BBNumbering[Succ] = 0;
            }
          }
        }
      }
    }

    // 使用随机种子打乱顺序
    long seed = RandomEngine.get_uint32_t();
    std::default_random_engine e(seed);
    std::shuffle(BBTargets.begin(), BBTargets.end(), e);

    unsigned N = 0;
    for (auto BB:BBTargets) {
      // 对每个目标基本块进行编号
      BBNumbering[BB] = N++;
    }
  }

  /**
   * 为函数的间接跳转（Indirect Branch）构建一个加密的跳转表（Jump Table），
   * 并返回对应的全局变量。这个技术通常用于代码混淆（Obfuscation），目的是增加逆向分析的难度。
   *
   * 获取/创建全局变量用于存储加密后的间接跳转地址（模式0）
   *
   * @param F 目标函数（需要保护其控制流）。
   * @param EncKey 加密密钥（用于计算跳转目标的偏移量）。
   * @return 存储加密跳转表的全局变量（例如 @funcName_IndirectBrTargets）。
   */
  GlobalVariable *getIndirectTargets0(Function &F, ConstantInt *EncKey) const {
    // 检查是否已经存在 函数名_IndirectBrTargets 全局变量
    std::string GVName(F.getName().str() + "_IndirectBrTargets");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV) {
      // 存在，直接返回。
      return GV;
    }

    // 加密并构建跳转表元素
    // encrypt branch targets
    std::vector<Constant *> Elements;
    int BBTargetIndex = 0;

    // 遍历函数的基本块（BBTargets），计算每个基本块的加密地址。
    for (const auto BB:BBTargets) {
      // 获得基本块地址，例如：ptr blockaddress(@_Z9calculateddc, %if.else)
      BlockAddress *BlockAddr = BlockAddress::get(BB);
      /*
       构造一个指向默认地址空间（地址空间零）中的对象的不透明指针，返回的类型是ptr
       例如：ptr
       */
      PointerType *BlockAddrDstTy = PointerType::getUnqual(F.getContext());
      /*
       基本块地址转换成ptr类型
       例如：ptr blockaddress(@_Z9calculateddc, %if.else)
       */
      const Constant *BlockAddrPtr = ConstantExpr::getBitCast(BlockAddr, BlockAddrDstTy);

      // 指针步长，例如：i8
      Type *ElementPtrInt8Ty = Type::getInt8Ty(F.getContext());

      /*
       GEP指令通用格式
       <result> = getelementptr <element-type>, <ptr-type> <ptrval>, <index-type> <index> [, <index-type> <index>]*

       打印内容举例：
       ptr getelementptr (i8, ptr blockaddress(@_Z9calculateddc, %if.else), i64 7407434676487839686)

        1. 返回类型: ptr - 表示返回一个指针
        2. element-type (i8)：这指定了指针算术的"步长单位"，表示计算偏移量时以字节(8位)为单位
        3. 基础指针值: blockaddress(@_Z9calculateddc, %if.else)
          - @_Z9calculateddc 是一个函数，可能是经过名称修饰的 calculate 函数
          - %if.else 是该函数中的一个基本块(label)
          - blockaddress() 获取这个基本块的地址
        4. 偏移量: i64 7407434676487839686 (十六进制: 0x66CC9527B5B5B5C6)
          - 这是一个非常大的偏移量，看起来不太像常规的内存偏移
          - 可能是某种混淆或加密技术的一部分

       使用 GEP 进行“加密”：
        计算 BlockAddrPtr + EncKey（即 ptr + offset）。
        这里的 EncKey 是一个大整数（如 7407434676487839686），使得逆向分析时难以直接恢复原始地址。
        由于 ElementPtrInt8Ty 是 i8（字节），偏移量按字节计算。
      */
      Constant *CE = ConstantExpr::getGetElementPtr(
          ElementPtrInt8Ty, const_cast<Constant *>(BlockAddrPtr), EncKey);

      // CE->print(outs());
//      outs() << CE << "\n\n";

      outs() << "[" << TAG << "] " << BBTargetIndex
             << ". EncKey:" << EncKey->getValue()
             << ". EncKeyTy:" << EncKey->getType()
             << ",BlockAddress:" << *BlockAddr
             << ",ElementPtrInt8Ty:" << *ElementPtrInt8Ty
             << ",BlockAddrDstTy:" << *BlockAddrDstTy
             << ",OldBlockAddress:" << *BlockAddrPtr
             << ",NewBlockAddress:" << *CE
             << "\n";

      Elements.push_back(CE);

      BBTargetIndex++;
    }

    PointerType *ElementType = PointerType::getUnqual(F.getContext());
    // 定义一个指针数组类型（[N x ptr]）。
    ArrayType *ATy =
        ArrayType::get(ElementType, Elements.size());
    outs() << "[" << TAG << "] ElementType:" << *ElementType
           << ",Size:" << Elements.size()
           << ",ATy:" << ATy
           << "\n";

    // 将加密后的跳转目标存入常量数组。
    Constant *CA = ConstantArray::get(ATy, ArrayRef<Constant *>(Elements));

    outs() << "[" << TAG << "] Constant:" << *CA << "\n\n";

    // 创建一个全局变量存储该数组
    GV = new GlobalVariable(*F.getParent(), ATy, false, GlobalValue::LinkageTypes::PrivateLinkage,
                                               CA, GVName);
    appendToCompilerUsed(*F.getParent(), {GV});
    return GV;
  }

  // 获取/创建全局变量用于存储加密后的间接跳转地址（模式1）
  GlobalVariable *getIndirectTargets1(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) const {
    std::string GVName(F.getName().str() + "_IndirectBrTargets1");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    // 加密跳转地址：使用异或+加法密钥
    // encrypt branch targets
    std::vector<Constant *> Elements;
    for (const auto BB:BBTargets) {
      Constant *CE = ConstantExpr::getBitCast(BlockAddress::get(BB), PointerType::getUnqual(F.getContext()));
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

  // 获取/创建全局变量用于存储加密后的间接跳转地址（模式2）
  GlobalVariable *getIndirectTargets2(Function &F, ConstantInt *AddKey, ConstantInt *XorKey) {
    std::string GVName(F.getName().str() + "_IndirectBrTargets2");
    GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
    if (GV)
      return GV;

    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }
    // 加密跳转地址：结合基本块编号、乘法和异或操作
    // encrypt branch targets
    std::vector<Constant *> Elements;
    for (auto BB:BBTargets) {
      Constant *CE = ConstantExpr::getBitCast(BlockAddress::get(BB), PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, BBNumbering[BB], false))));
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

  // 获取/创建两个全局变量，分别存储加法和异或加密参数（模式3）
  std::pair<GlobalVariable *, GlobalVariable *> getIndirectTargets3(Function &F, ConstantInt *AddKey) {
    std::string GVNameAdd(F.getName().str() + "_IndirectBrTargets3");
    std::string GVNameXor(F.getName().str() + "_IndirectBr3_Xor");
    GlobalVariable *GVAdd = F.getParent()->getNamedGlobal(GVNameAdd);
    GlobalVariable *GVXor = F.getParent()->getNamedGlobal(GVNameXor);

    if (GVAdd && GVXor)
      return std::make_pair(GVAdd, GVXor);

    auto& Ctx = F.getContext();
    IntegerType *intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    // 每个基本块使用不同的异或密钥
    // encrypt branch targets
    std::vector<Constant *> Elements;
    std::vector<Constant *> XorKeys;
    for (auto BB:BBTargets) {
      uint64_t V = RandomEngine.get_uint64_t();
      Constant *XorKey = ConstantInt::get(intType, V, false);
      Constant *CE = ConstantExpr::getBitCast(BlockAddress::get(BB), PointerType::getUnqual(F.getContext()));
      CE = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), CE, ConstantExpr::getXor(AddKey, ConstantExpr::getMul(XorKey, ConstantInt::get(intType, BBNumbering[BB], false))));

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


  // Pass 的主逻辑：对函数中的条件分支进行间接化处理
  bool runOnFunction(Function &Fn) override {

    const auto opt = ArgsOptions->toObfuscate(ArgsOptions->indBrOpt(), &Fn);

    if (!opt.isEnabled()) {
      return false;
    }

    if (Fn.empty() || Fn.hasLinkOnceLinkage() || Fn.getSection() == ".text.startup") {
      return false;
    }

//    if (Fn.getName().starts_with("goron_decrypt_string")) {
//      if (Fn.getName() != "goron_decrypt_string_1") {
//        return false;
//      }
//    }

    LLVMContext &Ctx = Fn.getContext();

    // 初始化成员字段
    // Init member fields
    BBNumbering.clear();
    BBTargets.clear();

    // 分割临界边以确保安全替换分支指令
    // llvm cannot split critical edge from IndirectBrInst
    CriticalEdgeSplittingOptions criticalEdgeSplittingOptions(nullptr, nullptr);
    criticalEdgeSplittingOptions.setMergeIdenticalEdges();
    SplitAllCriticalEdges(Fn, criticalEdgeSplittingOptions);
    // 遍历函数中的所有基本块，识别条件分支，并收集目标基本块
    NumberBasicBlock(Fn);

    if (BBNumbering.empty()) {
      return false;
    }

    // 获取两个64位随机数
//    const uint64_t V = RandomEngine.get_uint64_t();
    const uint64_t XV = RandomEngine.get_uint64_t();
    // 如果随机数是64位的，在MacOS上构建的时候用我们自己编译的链接器 ld64.lld 会出错，我试了一下随机数是32位的加密key没有问题
    const uint64_t V = RandomEngine.get_uint32_t();
//    const uint64_t V = 3740; // 3740左右的数字，在MacOS上用这个数字混淆，如果用的是系统的链接器，执行生成的可执行文件会报段错误
//    const uint64_t V = 9;
    const uint64_t V1 = -V;
//    const uint64_t XV = RandomEngine.get_uint64_t();

    // 根据系统指针大小确定整数类型（32位或64位）
    IntegerType* intType = Type::getInt32Ty(Ctx);
    if (pointerSize == 8) {
      intType = Type::getInt64Ty(Ctx);
    }

    outs() << "[" << TAG << "] level:" << opt.level()
           << "V:" << V << ",XV:" << XV
           << ",BitWidth:" << intType->getBitWidth()
           << "\n\n";

    // 创建常量加密密钥
    ConstantInt *EncKey = ConstantInt::get(intType, V, false);
    ConstantInt *EncKey1 = ConstantInt::get(intType, V1, false);
    ConstantInt *Zero = ConstantInt::get(intType, 0);

    // 声明全局变量（用于存储加密数据）
    GlobalVariable *GXorKey = nullptr;  // 异或密钥
    GlobalVariable *DestBBs = nullptr;  // 目标基本块数组
    GlobalVariable *XorKeys = nullptr;  // 异或密钥数组

    // 根据不同级别选择不同的加密方式
    if (opt.level() == 0) {
      // 级别0：基本加密

      DestBBs = getIndirectTargets0(Fn, EncKey1);
    } else if (opt.level() == 1 || opt.level() == 2) {
      // 级别1和2：使用额外的异或密钥

      ConstantInt *CXK = ConstantInt::get(intType, XV, false);

      // 创建全局变量存储异或密钥
      GXorKey = new GlobalVariable(*Fn.getParent(), CXK->getType(), false, GlobalValue::LinkageTypes::PrivateLinkage,
        CXK, Fn.getName() + "_IBrXorKey");
      appendToCompilerUsed(*Fn.getParent(), {GXorKey});
      if (opt.level() == 1) {
        // 级别1：使用简单异或加密
        DestBBs = getIndirectTargets1(Fn, EncKey1, CXK);
      } else {
        // 级别2：使用带索引乘法的异或加密
        DestBBs = getIndirectTargets2(Fn, EncKey1, CXK);
      }
    } else {
      // 级别3：最复杂的加密方式，使用密钥数组
      auto [fst, snd] = getIndirectTargets3(Fn, EncKey1);
      DestBBs = fst;
      XorKeys = snd;
    }

    // 遍历函数中的所有基本块，替换条件分支为间接跳转
    for (auto &BB : Fn) {
      // 获取终止指令
      auto *BI = dyn_cast<BranchInst>(BB.getTerminator());

      if (BI == nullptr || !BI->isConditional()) {
        continue;
      }

      // 是条件分支

      // 创建IR构建器
      IRBuilder<> IRB(BI);

      // 获取条件值和两个目标基本块的索引
      Value *Cond = BI->getCondition();
      Value *Idx;
      Value *TIdx, *FIdx;

      // 获取两个后继基本块的编号
      TIdx = ConstantInt::get(intType, BBNumbering[BI->getSuccessor(0)]);
      FIdx = ConstantInt::get(intType, BBNumbering[BI->getSuccessor(1)]);

      // 根据条件选择索引
      Idx = IRB.CreateSelect(Cond, TIdx, FIdx);

      // 计算加密目标地址的指针
      Value *GEP = IRB.CreateGEP(
          DestBBs->getValueType(), DestBBs,
          {Zero, Idx});
      Value *EncDestAddr = IRB.CreateLoad(
          GEP->getType(),
          GEP,
          "EncDestAddr");

      // 计算解密密钥
      // -EncKey = X - FuncSecret
      Value *DecKey = EncKey;

      // 根据混淆级别计算不同的解密密钥
      if (GXorKey) {
        LoadInst *XorKey = IRB.CreateLoad(GXorKey->getValueType(), GXorKey);

        if (opt.level() == 1) {
          // 级别1解密方式： (V1 XOR XorKey)的负数
          DecKey = IRB.CreateXor(EncKey1, XorKey);
          DecKey = IRB.CreateNeg(DecKey);
        } else if (opt.level() == 2) {
          // 级别2解密方式： (V1 XOR (XorKey * Idx))的负数
          DecKey = IRB.CreateXor(EncKey1, IRB.CreateMul(XorKey, Idx));
          DecKey = IRB.CreateNeg(DecKey);
        }
      }

      // 级别3的特殊解密处理
      if (XorKeys) {
        // 从密钥数组加载对应索引的密钥
        Value *XorKeysGEP = IRB.CreateGEP(XorKeys->getValueType(), XorKeys, {Zero, Idx});

        Value *XorKey = IRB.CreateLoad(intType, XorKeysGEP);

        // 复杂的密钥计算过程
        XorKey = IRB.CreateNeg(XorKey);
        XorKey = IRB.CreateXor(XorKey, EncKey1);
        XorKey = IRB.CreateNeg(XorKey);

        // 最终解密密钥计算
        DecKey = IRB.CreateXor(EncKey1, IRB.CreateMul(XorKey, Idx));
        DecKey = IRB.CreateNeg(DecKey);
      }

      // 解密目标地址
      Value *DestAddr = IRB.CreateGEP(
          Type::getInt8Ty(Ctx),
          EncDestAddr, DecKey);

      // 创建间接跳转指令并替换原分支
      IndirectBrInst *IBI = IndirectBrInst::Create(DestAddr, 2);
      // 添加第一个目标
      IBI->addDestination(BI->getSuccessor(0));
      // 添加第二个目标
      IBI->addDestination(BI->getSuccessor(1));
      // 替换指令
      ReplaceInstWithInst(BI, IBI);
    }

    return true;
  }

};
} // namespace llvm

char IndirectBranch::ID = 0;
FunctionPass *llvm::createIndirectBranchPass(unsigned pointerSize, ObfuscationOptions *argsOptions) {
  return new IndirectBranch(pointerSize, argsOptions);
}
INITIALIZE_PASS(IndirectBranch, "indbr", "Enable IR Indirect Branch Obfuscation", false, false)
