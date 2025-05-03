#include "llvm/Transforms/Obfuscation/ObfuscationOptions.h"
#include "llvm/Transforms/Obfuscation/StringEncryption.h"
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
#include <map>
#include <set>
#include <iostream>
#include <algorithm>

#define DEBUG_TYPE "string-encryption"

using namespace llvm;
namespace {
struct StringEncryption : public ModulePass {
  static char ID;

  struct CSPEntry {
    CSPEntry() : ID(0), Offset(0), DecGV(nullptr), DecStatus(nullptr), DecFunc(nullptr) {}
    unsigned ID;
    unsigned Offset;
    GlobalVariable *DecGV;
    GlobalVariable *DecStatus; // is decrypted or not
    std::vector<uint8_t> Data;
    std::vector<uint8_t> EncKey;
    Function *DecFunc;
  };

  struct CSUser {
    CSUser(Type* ETy, GlobalVariable *User, GlobalVariable *NewGV)
        : Ty(ETy), GV(User), DecGV(NewGV), DecStatus(nullptr),
          InitFunc(nullptr) {}
    Type *Ty;
    GlobalVariable *GV;
    GlobalVariable *DecGV;
    GlobalVariable *DecStatus; // is decrypted or not
    Function *InitFunc; // InitFunc will use decryted string to initialize DecGV
  };

  ObfuscationOptions *ArgsOptions;
  CryptoUtils RandomEngine;
  std::vector<CSPEntry *> ConstantStringPool;
  std::map<GlobalVariable *, CSPEntry *> CSPEntryMap;
  std::map<GlobalVariable *, CSUser *> CSUserMap;
  GlobalVariable *EncryptedStringTable = nullptr;
  std::set<GlobalVariable *> MaybeDeadGlobalVars;

  StringEncryption(ObfuscationOptions *argsOptions) : ModulePass(ID) {
    this->ArgsOptions = argsOptions;
    initializeStringEncryptionPass(*PassRegistry::getPassRegistry());
  }

  bool doFinalization(Module &) override {
    for (CSPEntry *Entry : ConstantStringPool) {
      delete (Entry);
    }
    for (auto &I : CSUserMap) {
      CSUser *User = I.second;
      delete (User);
    }
    ConstantStringPool.clear();
    CSPEntryMap.clear();
    CSUserMap.clear();
    MaybeDeadGlobalVars.clear();
    return false;
  }

  StringRef getPassName() const override { return {"StringEncryption"}; }

  bool runOnModule(Module &M) override;
  static void collectConstantStringUser(GlobalVariable *CString, std::set<GlobalVariable *> &Users);
  static bool isValidToEncrypt(GlobalVariable *GV);
  bool processConstantStringUse(Function *F);
  void deleteUnusedGlobalVariable();
  static Function *buildDecryptFunction(Module *M, const CSPEntry *Entry);
  Function *buildInitFunction(Module *M, const CSUser *User);
  void getRandomBytes(std::vector<uint8_t> &Bytes, uint32_t MinSize, uint32_t MaxSize);
  void lowerGlobalConstant(Constant *CV, IRBuilder<> &IRB, Value *Ptr, Type *Ty);
  void lowerGlobalConstantStruct(ConstantStruct *CS, IRBuilder<> &IRB, Value *Ptr, Type *Ty);
  void lowerGlobalConstantArray(ConstantArray *CA, IRBuilder<> &IRB, Value *Ptr, Type *Ty);
};
} // namespace llvm

char StringEncryption::ID = 0;
bool StringEncryption::runOnModule(Module &M) {
  // 存储常量字符串用户的集合
  std::set<GlobalVariable *> ConstantStringUsers;

  // collect all c strings

  // 获取模块上下文
  LLVMContext &Ctx = M.getContext();
  // 创建一个整型常量0
  ConstantInt *Zero = ConstantInt::get(Type::getInt32Ty(Ctx), 0);
  // 遍历模块中的所有全局变量
  for (GlobalVariable &GV : M.globals()) {
    // 如果不是常量或没有初始化器，或者有DLL导出/导入存储类，则跳过
    if (!GV.isConstant() || !GV.hasInitializer() ||
      GV.hasDLLExportStorageClass() || GV.isDLLImportDependent()) {
      continue;
    }
    // 获取初始值
    Constant *Init = GV.getInitializer();
    if (Init == nullptr)
      continue;
    // 检查是否为顺序常量数据类型
    if (ConstantDataSequential *CDS = dyn_cast<ConstantDataSequential>(Init)) {
      // 判断是否是C字符串
      if (CDS->isCString()) {
        // 创建新的CSPEntry实例
        CSPEntry *Entry = new CSPEntry();
        // 获取原始数据值
        StringRef Data = CDS->getRawDataValues();
        // 预留空间
        Entry->Data.reserve(Data.size());
        for (unsigned i = 0; i < Data.size(); ++i) {
          // 将每个字符转换为uint8_t并添加到Entry->Data中
          Entry->Data.push_back(static_cast<uint8_t>(Data[i]));
        }
        // 设置ID
        Entry->ID = static_cast<unsigned>(ConstantStringPool.size());
        // 创建零值常量
        Constant *ZeroInit = Constant::getNullValue(CDS->getType());
        // 创建一个新的全局变量用于解密后的字符串
        GlobalVariable *DecGV = new GlobalVariable(M, CDS->getType(), false, GlobalValue::PrivateLinkage,
                                                   ZeroInit, "dec" + Twine::utohexstr(Entry->ID) + GV.getName());
        // 创建一个状态变量用于跟踪解密状态
        GlobalVariable *DecStatus = new GlobalVariable(M, Type::getInt32Ty(Ctx), false, GlobalValue::PrivateLinkage,
                                                   Zero, "dec_status_" + Twine::utohexstr(Entry->ID) + GV.getName());
        // 设置对齐方式
        DecGV->setAlignment(MaybeAlign(GV.getAlignment()));
        // 设置解密后的全局变量
        Entry->DecGV = DecGV;
        // 设置解密状态变量
        Entry->DecStatus = DecStatus;
        // 添加到常量字符串池
        ConstantStringPool.push_back(Entry);
        // 映射全局变量到对应的CSPEntry
        CSPEntryMap[&GV] = Entry;
        // 收集使用该常量字符串的用户
        collectConstantStringUser(&GV, ConstantStringUsers);
      }
    }
  }

  // 加密字符串，并构建对应的解密函数
  // encrypt those strings, build corresponding decrypt function
  for (CSPEntry *Entry: ConstantStringPool) {
    // 获取随机字节作为加密密钥
    getRandomBytes(Entry->EncKey, 16, 32);
    // 上一个明文字母
    uint8_t LastPlainChar = 0;
    for (unsigned i = 0; i < Entry->Data.size(); ++i) {
      const uint32_t KeyIndex = i % Entry->EncKey.size();
      const uint8_t CurrentKey = Entry->EncKey[KeyIndex];
      const uint8_t CurrentPlainChar = Entry->Data[i];
      // 异或操作加密
      Entry->Data[i] ^= CurrentKey;
      // 根据特定条件进一步混淆
      if ((KeyIndex * CurrentKey) % 2 == 0) {
        // 取反
        Entry->Data[i] = ~Entry->Data[i];
        // 再次异或
        Entry->Data[i] ^= CurrentKey;
        // 减去上一个明文字母
        Entry->Data[i] = Entry->Data[i] - LastPlainChar;
      } else {
        // 取负数
        Entry->Data[i] = -Entry->Data[i];
        // 异或
        Entry->Data[i] ^= CurrentKey;
        // 加上上一个明文字母
        Entry->Data[i] = Entry->Data[i] + LastPlainChar;
      }
      // 更新上一个明文字母
      LastPlainChar = CurrentPlainChar;
    }
    // 构建解密函数
    Entry->DecFunc = buildDecryptFunction(&M, Entry);
  }

  // 构建支持的常量字符串用户的初始化函数
  // build initialization function for supported constant string users
  for (GlobalVariable *GV: ConstantStringUsers) {
    if (isValidToEncrypt(GV)) {
      // 获取元素类型
      Type *EltType = GV->getValueType();
      // 创建零值常量
      Constant *ZeroInit = Constant::getNullValue(EltType);
      // 创建新的全局变量用于存放解密后的字符串
      GlobalVariable *DecGV = new GlobalVariable(M, EltType, false, GlobalValue::PrivateLinkage,
                                                 ZeroInit, "dec_" + GV->getName());
      DecGV->setAlignment(MaybeAlign(GV->getAlignment()));
      // 创建解密状态变量
      GlobalVariable *DecStatus = new GlobalVariable(M, Type::getInt32Ty(Ctx), false, GlobalValue::PrivateLinkage,
          Zero, "dec_status_" + GV->getName());
      // 创建CSUser实例
      CSUser *User = new CSUser(EltType, GV, DecGV);
      // 设置解密状态变量
      User->DecStatus = DecStatus;
      // 构建初始化函数
      User->InitFunc = buildInitFunction(&M, User);
      // 映射全局变量到对应的CSUser
      CSUserMap[GV] = User;
    }
  }

  // 发布加密字符串表
  // emit the constant string pool
  // | junk bytes | key 1 | encrypted string 1 | junk bytes | key 2 | encrypted string 2 | ...
  // 数据向量
  std::vector<uint8_t> Data;
  // 垃圾字节向量
  std::vector<uint8_t> JunkBytes;

  // 预留垃圾字节向量的空间
  JunkBytes.reserve(32);
  for (CSPEntry *Entry: ConstantStringPool) {
    // 清空垃圾字节向量
    JunkBytes.clear();
    // 获取随机垃圾字节
    getRandomBytes(JunkBytes, 16, 32);
    // 插入垃圾字节到数据向量
    Data.insert(Data.end(), JunkBytes.begin(), JunkBytes.end());
    // 记录偏移量
    Entry->Offset = static_cast<unsigned>(Data.size());
    // 插入加密密钥
    Data.insert(Data.end(), Entry->EncKey.begin(), Entry->EncKey.end());
    // 插入加密的数据
    Data.insert(Data.end(), Entry->Data.begin(), Entry->Data.end());
  }

  // 创建包含加密字符串表的全局变量
  Constant *CDA = ConstantDataArray::get(M.getContext(), ArrayRef<uint8_t>(Data));
  EncryptedStringTable = new GlobalVariable(M, CDA->getType(), false, GlobalValue::PrivateLinkage,
                                            CDA, "EncryptedStringTable");

  // 是否修改标志
  // decrypt string back at every use, change the plain string use to the decrypted one
  bool Changed = false;
  for (Function &F:M) {
    if (F.isDeclaration())
      continue;
    // 处理常量字符串使用
    Changed |= processConstantStringUse(&F);
  }

  for (auto &I : CSUserMap) {
    CSUser *User = I.second;
    // 处理初始化函数中的常量字符串使用
    Changed |= processConstantStringUse(User->InitFunc);
  }

  // 删除未使用的全局变量
  // delete unused global variables
  deleteUnusedGlobalVariable();
  for (CSPEntry *Entry: ConstantStringPool) {
    if (Entry->DecFunc->use_empty()) {
      // 删除无用的解密函数
      Entry->DecFunc->eraseFromParent();
    }
  }
  return Changed;
}

// 辅助函数：生成指定范围内的随机字节数组
void StringEncryption::getRandomBytes(std::vector<uint8_t> &Bytes, uint32_t MinSize, uint32_t MaxSize) {
  // 获取随机数
  uint32_t N = RandomEngine.get_uint32_t();
  uint32_t Len;

  // 确保最大尺寸不小于最小尺寸
  assert(MaxSize >= MinSize);

  if (MinSize == MaxSize) {
    // 如果最小和最大相同，直接使用
    Len = MinSize;
  } else {
    // 否则，计算长度
    Len = MinSize + (N % (MaxSize - MinSize));
  }

  // 分配内存
  char *Buffer = new char[Len];
  // 填充随机字节
  RandomEngine.get_bytes(Buffer, Len);
  for (uint32_t i = 0; i < Len; ++i) {
    // 转换并添加到字节向量
    Bytes.push_back(static_cast<uint8_t>(Buffer[i]));
  }

  // 释放内存
  delete[] Buffer;
}

//
//static void goron_decrypt_string(uint8_t *plain_string, const uint8_t *data)
//{
//  const uint8_t *key = data;
//  uint32_t key_size = 1234;
//  uint8_t *es = (uint8_t *) &data[key_size];
//  uint32_t i;
//  uint8_t last_decrypted_char = 0;
//  for (i = 0;i < 5678;i ++) {
//    uint32_t key_index = i % key_size;
//    uint8_t current_key = key[key_index];
//    uint8_t ds;
//    if ((key_index * current_key) % 2 == 0) {
//      ds = es[i] + last_decrypted_char;
//      ds = ds ^ current_key;
//      ds = ~ds;
//    } else {
//      ds = es[i] - last_decrypted_char;
//      ds = ds ^ current_key;
//      ds = -ds;
//    }
//    ds = ds ^ current_key;
//    last_decrypted_char = ds;
//    plain_string[i] = ds;
//  }
//}

Function *StringEncryption::buildDecryptFunction(Module *M, const StringEncryption::CSPEntry *Entry) {
  LLVMContext &Ctx = M->getContext();
  IRBuilder<> IRB(Ctx);
  FunctionType *FuncTy = FunctionType::get(
      Type::getVoidTy(Ctx),
      {PointerType::getUnqual(Ctx), PointerType::getUnqual(Ctx)},
      false);
  // 创建解密函数：返回 void，接受两个指针参数（明文字符串输出、加密数据输入）
  Function *DecFunc =
      Function::Create(FuncTy, GlobalValue::PrivateLinkage, "goron_decrypt_string_" + Twine::utohexstr(Entry->ID), M);

  auto ArgIt = DecFunc->arg_begin();
  // 第一个参数：解密后的明文字符串输出地址
  Argument *PlainString = ArgIt; // output
  ++ArgIt;
  // 第二个参数：包含加密数据的输入结构体
  Argument *Data = ArgIt;       // input

  PlainString->setName("plain_string");
  // 表示该参数不会被捕获
  PlainString->addAttr(Attribute::NoCapture);
  Data->setName("data");
  // 同上
  Data->addAttr(Attribute::NoCapture);

  // 创建基本块
  BasicBlock *Enter = BasicBlock::Create(Ctx, "Enter", DecFunc);
  BasicBlock *LoopBody = BasicBlock::Create(Ctx, "LoopBody", DecFunc);
  BasicBlock *LoopBr0 = BasicBlock::Create(Ctx, "LoopBr0", DecFunc);
  BasicBlock *LoopBr1 = BasicBlock::Create(Ctx, "LoopBr1", DecFunc);
  BasicBlock *LoopEnd = BasicBlock::Create(Ctx, "LoopEnd", DecFunc);
  BasicBlock *UpdateDecStatus = BasicBlock::Create(Ctx, "UpdateDecStatus", DecFunc);
  BasicBlock *Exit = BasicBlock::Create(Ctx, "Exit", DecFunc);

  IRB.SetInsertPoint(Enter);
  // 获取密钥长度
  ConstantInt *KeySize = ConstantInt::get(Type::getInt32Ty(Ctx), Entry->EncKey.size());
  // 计算加密数据起始地址
  Value *EncPtr = IRB.CreateInBoundsGEP(IRB.getInt8Ty(), Data, KeySize);
  // 加载当前解密状态
  Value *DecStatus = IRB.CreateLoad(
      Entry->DecStatus->getValueType(), Entry->DecStatus);
  // 检查是否已经解密过
  Value *IsDecrypted = IRB.CreateICmpEQ(DecStatus, IRB.getInt32(1));
  // 如果已解密，跳转到退出块
  IRB.CreateCondBr(IsDecrypted, Exit, LoopBody);

  IRB.SetInsertPoint(LoopBody);
  // 循环计数器
  PHINode *LoopCounter = IRB.CreatePHI(IRB.getInt32Ty(), 2);
  // 初始值为0
  LoopCounter->addIncoming(IRB.getInt32(0), Enter);

  // 上一个解密出的字符
  PHINode *LastDecrypted = IRB.CreatePHI(IRB.getInt8Ty(), 2);
  // 初始值为0
  LastDecrypted->addIncoming(IRB.getInt8(0), Enter);

  // 当前加密字符地址
  Value *EncCharPtr =
      IRB.CreateInBoundsGEP(IRB.getInt8Ty(), EncPtr,
      LoopCounter);
  // 加载当前加密字符
  Value *EncChar = IRB.CreateLoad(IRB.getInt8Ty(), EncCharPtr, true);
  // 密钥索引 = 循环计数 % 密钥长度
  Value *KeyIdx = IRB.CreateURem(LoopCounter, KeySize);

  // 密钥字符地址
  Value *KeyCharPtr = IRB.CreateInBoundsGEP(IRB.getInt8Ty(), Data, KeyIdx);
  // 加载密钥字符
  Value *KeyChar = IRB.CreateLoad(IRB.getInt8Ty(), KeyCharPtr);

  //====================Initialized=========================

  // BrKey = (KeyIdx * zero-extended KeyChar) & 1
  // 用于判断进入哪个分支（%2 == 0 或 %2 == 1）
  Value *BrKey = IRB.CreateAnd(IRB.CreateMul(KeyIdx, IRB.CreateZExt(KeyChar, KeyIdx->getType(), "", true), "", true, true), IRB.getInt32(1));
  // 若结果为0，则跳转到 LoopBr0
  Value *BrCond = IRB.CreateICmpEQ(BrKey, IRB.getInt32(0));
  // 条件跳转
  // If zero, %2 == 0;
  IRB.CreateCondBr(BrCond, LoopBr0, LoopBr1);

  // Loop0 Start - %2 == 0;
  IRB.SetInsertPoint(LoopBr0);
  // 解密方式0: 加法 + 异或 + 取反
  Value *DecChar0 = IRB.CreateAdd(EncChar, LastDecrypted);
  DecChar0 = IRB.CreateXor(DecChar0, KeyChar);
  DecChar0 = IRB.CreateNot(DecChar0);
  // 跳转至合并块
  IRB.CreateBr(LoopEnd);

  // Loop1 Start - %2 == 1;
  IRB.SetInsertPoint(LoopBr1);
  // 解密方式1: 减法 + 异或 + 取负
  Value *DecChar1 = IRB.CreateSub(EncChar, LastDecrypted);
  DecChar1 = IRB.CreateXor(DecChar1, KeyChar);
  DecChar1 = IRB.CreateNeg(DecChar1);
  // 跳转至合并块
  IRB.CreateBr(LoopEnd);

  // LoopEnd and finally decrypt current char
  IRB.SetInsertPoint(LoopEnd);
  // 合并两个分支的解密结果
  PHINode *BrDecChar = IRB.CreatePHI(IRB.getInt8Ty(), 2);
  BrDecChar->addIncoming(DecChar0, LoopBr0);
  BrDecChar->addIncoming(DecChar1, LoopBr1);
  // 最终再异或一次密钥字符
  Value *DecChar = IRB.CreateXor(BrDecChar, KeyChar);

  // 更新上一个解密字符
  //Store
  LastDecrypted->addIncoming(DecChar, LoopEnd);
  // 当前明文字符地址
  Value *DecCharPtr = IRB.CreateInBoundsGEP(IRB.getInt8Ty(),
      PlainString, LoopCounter);
  // 存储解密字符
  IRB.CreateStore(DecChar, DecCharPtr);

  // 计数器+1
  Value *NewCounter = IRB.CreateAdd(LoopCounter, IRB.getInt32(1), "", true, true);
  // 更新 PHI 值
  LoopCounter->addIncoming(NewCounter, LoopEnd);

  // 是否完成所有字符？
  Value *Cond = IRB.CreateICmpEQ(NewCounter, IRB.getInt32(static_cast<uint32_t>(Entry->Data.size())));
  // 是则更新状态，否则继续循环
  IRB.CreateCondBr(Cond, UpdateDecStatus, LoopBody);

  IRB.SetInsertPoint(UpdateDecStatus);
  // 标记为已解密
  IRB.CreateStore(IRB.getInt32(1), Entry->DecStatus);
  // 跳转至退出
  IRB.CreateBr(Exit);

  IRB.SetInsertPoint(Exit);
  // 返回 void
  IRB.CreateRetVoid();

  return DecFunc;
}

Function *StringEncryption::buildInitFunction(Module *M, const StringEncryption::CSUser *User) {
  LLVMContext &Ctx = M->getContext();
  IRBuilder<> IRB(Ctx);
  // 参数是全局变量指针
  FunctionType *FuncTy = FunctionType::get(Type::getVoidTy(Ctx), {User->DecGV->getType()}, false);
  Function *InitFunc =
      Function::Create(FuncTy, GlobalValue::PrivateLinkage, "__global_variable_initializer_" + User->GV->getName(), M);

  auto ArgIt = InitFunc->arg_begin();
  Argument *thiz = ArgIt;

  thiz->setName("this");
  // 不捕获 this 指针
  thiz->addAttr(Attribute::NoCapture);

  // convert constant initializer into a series of instructions
  BasicBlock *Enter = BasicBlock::Create(Ctx, "Enter", InitFunc);
  BasicBlock *InitBlock = BasicBlock::Create(Ctx, "InitBlock", InitFunc);
  BasicBlock *Exit = BasicBlock::Create(Ctx, "Exit", InitFunc);

  IRB.SetInsertPoint(Enter);
  // 加载解密状态
  Value *DecStatus = IRB.CreateLoad(
      User->DecStatus->getValueType(), User->DecStatus);
  // 是否已解密
  Value *IsDecrypted = IRB.CreateICmpEQ(DecStatus, IRB.getInt32(1));
  // 已解密则直接退出
  IRB.CreateCondBr(IsDecrypted, Exit, InitBlock);

  IRB.SetInsertPoint(InitBlock);
  // 获取原始初始化常量
  Constant *Init = User->GV->getInitializer();
  // 将常量转换为指令写入内存
  lowerGlobalConstant(Init, IRB, User->DecGV, User->Ty);
  // 设置解密标志为已解密
  IRB.CreateStore(IRB.getInt32(1), User->DecStatus);
  // 跳转至退出块
  IRB.CreateBr(Exit);

  IRB.SetInsertPoint(Exit);
  // 返回 void
  IRB.CreateRetVoid();
  return InitFunc;
}

void StringEncryption::lowerGlobalConstant(Constant *CV, IRBuilder<> &IRB, Value *Ptr, Type *Ty) {
  if (isa<ConstantAggregateZero>(CV)) {
    // 存储零初始化
    IRB.CreateStore(CV, Ptr);
    return;
  }

  if (ConstantArray *CA = dyn_cast<ConstantArray>(CV)) {
    // 处理数组类型常量
    lowerGlobalConstantArray(CA, IRB, Ptr, Ty);
  } else if (ConstantStruct *CS = dyn_cast<ConstantStruct>(CV)) {
    // 处理结构体类型常量
    lowerGlobalConstantStruct(CS, IRB, Ptr, Ty);
  } else {
    // 其他情况直接存储常量
    IRB.CreateStore(CV, Ptr);
  }
}

void StringEncryption::lowerGlobalConstantArray(ConstantArray *CA, IRBuilder<> &IRB, Value *Ptr, Type *Ty) {
  for (unsigned i = 0, e = CA->getNumOperands(); i != e; ++i) {
    Constant *CV = CA->getOperand(i);
    // 计算元素地址
    Value *GEP = IRB.CreateGEP(Ty,
                      Ptr, {IRB.getInt32(0), IRB.getInt32(i)});
    // 递归处理每个元素
    lowerGlobalConstant(CV, IRB, GEP, CV->getType());
  }
}

void StringEncryption::lowerGlobalConstantStruct(ConstantStruct *CS, IRBuilder<> &IRB, Value *Ptr, Type *Ty) {
  for (unsigned i = 0, e = CS->getNumOperands(); i != e; ++i) {
    Constant* CV = CS->getOperand(i);
    // 计算字段地址
    Value *GEP = IRB.CreateGEP(Ty,
                      Ptr, {IRB.getInt32(0), IRB.getInt32(i)});
    // 递归处理每个字段
    lowerGlobalConstant(CV, IRB, GEP, CV->getType());
  }
}

bool StringEncryption::processConstantStringUse(Function *F) {
  // 判断当前函数是否需要混淆（根据配置选项）
  auto opt = ArgsOptions->toObfuscate(ArgsOptions->cseOpt(), F);
  if (!opt.isEnabled()) {
    return false;
  }

  LLVMContext &Ctx = F->getContext();

  // 将常量表达式降低为指令（使后续操作基于 IR 指令而非常量）
  LowerConstantExpr(*F);
  // 存储已解密的全局变量集合（防止在同一个基本块中重复解密）
  SmallPtrSet<GlobalVariable *, 16> DecryptedGV; // if GV has multiple use in a block, decrypt only at the first use
  bool Changed = false;

  // 遍历函数中的每个基本块
  for (BasicBlock &BB : *F) {
    // 每个基本块开始前清空状态
    DecryptedGV.clear();
    // 遍历基本块中的每条指令
    for (Instruction &Inst: BB) {
      if (PHINode *PHI = dyn_cast<PHINode>(&Inst)) {
        // 处理 PHI 节点中的使用情况（因为 PHI 的值依赖于来自不同块的输入）
        for (unsigned int i = 0; i < PHI->getNumIncomingValues(); ++i) {
          if (GlobalVariable *GV = dyn_cast<GlobalVariable>(PHI->getIncomingValue(i))) {
            // 查找是否是加密字符串
            auto Iter1 = CSPEntryMap.find(GV);
            // 查找是否是引用加密字符串的用户
            auto Iter2 = CSUserMap.find(GV);
            // GV 是一个常量字符串的使用者（如初始化器）
            if (Iter2 != CSUserMap.end()) { // GV is a constant string user
              CSUser *User = Iter2->second;
              if (DecryptedGV.count(GV) > 0) {
                // 如果已经解密过，则替换为此用户对应的解密后全局变量
                Inst.replaceUsesOfWith(GV, User->DecGV);
              } else {
                // 插入初始化调用（用于运行时解密）
                Instruction *InsertPoint = PHI->getIncomingBlock(i)->getTerminator();
                IRBuilder<> IRB(InsertPoint);
                // 创建初始化调用
                fixEH(IRB.CreateCall(User->InitFunc, {User->DecGV}));
                // 替换使用
                Inst.replaceUsesOfWith(GV, User->DecGV);
                // 标记原 GV 可能无用
                MaybeDeadGlobalVars.insert(GV);
                // 记录已处理
                DecryptedGV.insert(GV);
                Changed = true;
              }
            } else if (Iter1 != CSPEntryMap.end()) { // GV is a constant string
                                                     // GV 是加密字符串本身
              CSPEntry *Entry = Iter1->second;
              if (DecryptedGV.count(GV) > 0) {
                Inst.replaceUsesOfWith(GV, Entry->DecGV);
              } else {
                Instruction *InsertPoint = PHI->getIncomingBlock(i)->getTerminator();
                IRBuilder<> IRB(InsertPoint);

                // 构造解密函数参数：输出缓冲区和数据指针
                Value *OutBuf = IRB.CreateBitCast(Entry->DecGV,
                                                  PointerType::getUnqual(Ctx));
                Value *Data = IRB.CreateInBoundsGEP(
                    EncryptedStringTable->getValueType(),
                    EncryptedStringTable,
                    {IRB.getInt32(0), IRB.getInt32(Entry->Offset)});
                // 调用解密函数
                fixEH(IRB.CreateCall(Entry->DecFunc, {OutBuf, Data}));

                // 替换使用
                Inst.replaceUsesOfWith(GV, Entry->DecGV);
                MaybeDeadGlobalVars.insert(GV);
                DecryptedGV.insert(GV);
                Changed = true;
              }
            }
          }
        }
      } else {
        // 处理普通指令中的操作数
        for (User::op_iterator op = Inst.op_begin(); op != Inst.op_end(); ++op) {
          if (GlobalVariable *GV = dyn_cast<GlobalVariable>(*op)) {
            auto Iter1 = CSPEntryMap.find(GV);
            auto Iter2 = CSUserMap.find(GV);
            // 用户类型
            if (Iter2 != CSUserMap.end()) {
              CSUser *User = Iter2->second;
              if (DecryptedGV.count(GV) > 0) {
                Inst.replaceUsesOfWith(GV, User->DecGV);
              } else {
                IRBuilder<> IRB(&Inst);
                fixEH(IRB.CreateCall(User->InitFunc, {User->DecGV}));
                Inst.replaceUsesOfWith(GV, User->DecGV);
                MaybeDeadGlobalVars.insert(GV);
                DecryptedGV.insert(GV);
                Changed = true;
              }
            } else if (Iter1 != CSPEntryMap.end()) {
              // 加密字符串

              CSPEntry *Entry = Iter1->second;
              if (DecryptedGV.count(GV) > 0) {
                Inst.replaceUsesOfWith(GV, Entry->DecGV);
              } else {
                IRBuilder<> IRB(&Inst);
                
                // 准备解密函数参数并插入调用
                Value *OutBuf = IRB.CreateBitCast(Entry->DecGV,
                                                  PointerType::getUnqual(Ctx));
                Value *Data = IRB.CreateInBoundsGEP(
                    EncryptedStringTable->getValueType(),
                    EncryptedStringTable,
                    {IRB.getInt32(0), IRB.getInt32(Entry->Offset)});
                fixEH(IRB.CreateCall(Entry->DecFunc, {OutBuf, Data}));

                Inst.replaceUsesOfWith(GV, Entry->DecGV);
                MaybeDeadGlobalVars.insert(GV);
                DecryptedGV.insert(GV);
                Changed = true;
              }
            }
          }
        }
      }
    }
  }
  return Changed;
}

// 收集某个加密字符串的所有全局变量用户（递归查找）
void StringEncryption::collectConstantStringUser(GlobalVariable *CString, std::set<GlobalVariable *> &Users) {
  SmallPtrSet<Value *, 16> Visited;
  SmallVector<Value *, 16> ToVisit;

  ToVisit.push_back(CString);
  while (!ToVisit.empty()) {
    Value *V = ToVisit.pop_back_val();
    if (Visited.count(V) > 0)
      continue;
    Visited.insert(V);
    for (Value *User:V->users()) {
      if (auto *GV = dyn_cast<GlobalVariable>(User)) {
        // 找到全局变量用户
        Users.insert(GV);
      } else {
        // 否则继续搜索
        ToVisit.push_back(User);
      }
    }
  }
}

// 判断一个全局变量是否可以被加密（必须是常量且有初始值）
bool StringEncryption::isValidToEncrypt(GlobalVariable *GV) {
  if(GV->isConstant() && GV->hasInitializer()) {
    return GV->getInitializer() != nullptr;
  } else {
    return false;
  }
}

// 删除标记为可能死亡的全局变量（不再被使用）
void StringEncryption::deleteUnusedGlobalVariable() {
  bool Changed = true;
  while (Changed) {
    Changed = false;
    for (auto Iter = MaybeDeadGlobalVars.begin(); Iter != MaybeDeadGlobalVars.end();) {
      GlobalVariable *GV = *Iter;
      // 非本地链接的保留不删
      if (!GV->hasLocalLinkage()) {
        ++Iter;
        continue;
      }

      // 清除死常量用户
      GV->removeDeadConstantUsers();
      // 如果没有用户了
      if (GV->use_empty()) {
        if (GV->hasInitializer()) {
          Constant *Init = GV->getInitializer();
          GV->setInitializer(nullptr);
          if (isSafeToDestroyConstant(Init))
            // 销毁初始值
            Init->destroyConstant();
        }
        Iter = MaybeDeadGlobalVars.erase(Iter);
        // 从模块中删除该全局变量
        GV->eraseFromParent();
        Changed = true;
      } else {
        ++Iter;
      }
    }
  }
}

// 创建 StringEncryption Pass
ModulePass *llvm::createStringEncryptionPass(ObfuscationOptions *argsOptions) {
  return new StringEncryption(argsOptions);
}

// 注册 Pass
INITIALIZE_PASS(StringEncryption, "string-encryption", "Enable IR String Encryption", false, false)
