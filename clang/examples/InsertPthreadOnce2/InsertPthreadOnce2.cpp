#include <thread>
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Sema/Sema.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Lookup.h"
#include "llvm/ADT/StringRef.h"

using namespace clang;

class PthreadOncePPCallbacks : public PPCallbacks {
public:
  PthreadOncePPCallbacks(CompilerInstance &CI, bool ShouldInsert)
      : CI(CI), ShouldInsert(ShouldInsert) {}

  void FileChanged(SourceLocation Loc, FileChangeReason Reason,
                   SrcMgr::CharacteristicKind FileType,
                   FileID PrevFID) override {
    if (Reason == PPCallbacks::EnterFile && ShouldInsert) {
      InsertHeader();
      InsertGlobalVar();
    }
  }

  void EndOfMainFile() override {
    if (ShouldInsert) {
      llvm::errs() << "Plugin: End of main file reached\n";
//      InsertGlobalVar();
    }
  }

private:
  void InsertHeader() {
    if (InsertHeaderFinished) {
      return;
    }

    Preprocessor &PP = CI.getPreprocessor();
    SourceManager &SM = CI.getSourceManager();

    const FileID FD = SM.getMainFileID();
    if (FD.isInvalid()) {
      return;
    }

    InsertHeaderFinished = true;

    const SourceLocation SrcLoc = SM.getLocForStartOfFile(SM.getMainFileID());
    clang::StringRef FileName = SM.getFilename(SrcLoc);

    pthread_t tid = pthread_self();
    llvm::errs() << "Source:" << FileName << ",tid:" << tid << "\n";

    // 创建#include <pthread.h>指令
    std::string HeaderDirective = "#include <pthread.h>\n";
    std::unique_ptr<llvm::MemoryBuffer> Buffer =
        llvm::MemoryBuffer::getMemBufferCopy(HeaderDirective, "pthread_once_header");

    // 创建虚拟文件ID
    FileID PseudoFileID = SM.createFileID(
        std::move(Buffer),
//        SourceManager::C_User,
        clang::SrcMgr::C_User,
        /*LoadedID*/0, /*LoadedOffset*/0, SourceLocation()
    );

    // 添加到主文件之前
    SourceLocation IncludeLoc = SM.getLocForStartOfFile(FD);
    PP.EnterSourceFile(PseudoFileID, /*DirLookup*/nullptr, IncludeLoc);

    llvm::errs() << "Plugin: pthread.h header inserted. this=" << this << "\n";
  }

  void InsertGlobalVar() {
    if (InsertGlobalVarFinished) {
      return;
    }

    // 确保Sema已经创建
    if (!CI.hasSema()) {
      llvm::errs() << "Error: Sema not available at EndOfMainFile\n";
      return;
    }

    ASTContext &Context = CI.getASTContext();
    Sema &S = CI.getSema();

    // 查找或创建pthread_once_t类型
    DeclarationName Name = &Context.Idents.get("pthread_once_t");
    LookupResult R(S, Name, SourceLocation(), Sema::LookupOrdinaryName);

    if (!S.LookupName(R, S.TUScope)) {
//      llvm::errs() << "Error: pthread_once_t not found\n";
      return;
    }

    InsertGlobalVarFinished = true;

    QualType PthreadOnceType;
    if (TypeDecl *TD = R.getAsSingle<TypeDecl>()) {
      PthreadOnceType = Context.getTypeDeclType(TD);
    } else if (TypedefNameDecl *TND = R.getAsSingle<TypedefNameDecl>()) {
      PthreadOnceType = TND->getUnderlyingType();
    } else {
      llvm::errs() << "Error: Failed to determine pthread_once_t type\n";
      return;
    }

    // 创建全局变量声明
    IdentifierInfo *II = &Context.Idents.get("__pthread_once_global");
    TypeSourceInfo *TInfo = Context.getTrivialTypeSourceInfo(PthreadOnceType);
    SourceLocation Loc = Context.getTranslationUnitDecl()->getLocation();

    // 创建变量声明
    VarDecl *VD = VarDecl::Create(
        Context,
        Context.getTranslationUnitDecl(),
        Loc,
        Loc,
        II,
        PthreadOnceType,
        TInfo,
        StorageClass::SC_Extern
    );

    // 设置外部链接
//    VD->setStorageClass(StorageClass::SC_Extern);
//    VD->setLinkage(Linkage::ExternalLinkage);

    // 添加 used 属性防止优化
//    VD->addAttr(UsedAttr::CreateImplicit(
//        Context,
//        UsedAttr::GNU_used,
//        SourceRange()
//            ));
//    VD->addAttr(::new (Context) UsedAttr(
//        SourceRange(),
//        Context,
//        AttributeList::GNU_used
//        ));
    // 添加 used 属性防止优化 - 使用字符串方式
//    std::string UsedAttr = "used";
//    VD->addAttr(AnnotateAttr::CreateImplicit(Context, UsedAttr, SourceRange()));

    // 添加到AST
    Context.getTranslationUnitDecl()->addDecl(VD);


   // 验证变量已添加
   if (Context.getTranslationUnitDecl()->lookup(
                                           &Context.Idents.get("__pthread_once_global")).empty()) {
     llvm::errs() << "Error: Failed to add variable to AST\n";
   } else {
     llvm::errs() << "Plugin: Variable successfully added to AST\n";

     // 输出变量详细信息
     VarDecl *VD = dyn_cast<VarDecl>(*Context.getTranslationUnitDecl()->lookup(
                                                                          &Context.Idents.get("__pthread_once_global")).begin());
     if (VD) {
       llvm::errs() << "Variable type: ";
       VD->getType().dump();
       llvm::errs() << "Variable address: " << (void*)VD << "\n";
     }
   }

    llvm::errs() << "Plugin: Global variable __pthread_once_global inserted\n";
  }

  CompilerInstance &CI;
  bool ShouldInsert;

private:
  bool InsertHeaderFinished = false;
  bool InsertGlobalVarFinished = false;
};

// 自定义ASTConsumer确保在正确时机执行
class PluginASTConsumer : public ASTConsumer {
public:
  PluginASTConsumer() {}
};

class InsertPthreadOnceAction : public PluginASTAction {
protected:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(
      CompilerInstance &CI, llvm::StringRef) override {
//    llvm::errs() << "Plugin: CreateASTConsumer called\n";
    // 添加预处理器回调
    Preprocessor &PP = CI.getPreprocessor();
    PP.addPPCallbacks(std::make_unique<PthreadOncePPCallbacks>(CI, ShouldInsert));

    return std::make_unique<PluginASTConsumer>();
  }

  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &Args) override {
    for (const auto &Arg : Args) {
      if (Arg == "insert_pthread_once_t") {
        ShouldInsert = true;
        llvm::errs() << "Plugin: insert_pthread_once_t flag detected\n";
      }
    }
    return true;
  }

//  void ExecuteAction() override {
//    llvm::errs() << "Plugin: ExecuteAction called\n";
//
//    // 添加预处理器回调
//    Preprocessor &PP = getCompilerInstance().getPreprocessor();
//    PP.addPPCallbacks(std::make_unique<PthreadOncePPCallbacks>(getCompilerInstance(), ShouldInsert));
//
//    // 调用基类实现
//    PluginASTAction::ExecuteAction();
//  }

//  bool BeginSourceFileAction(CompilerInstance &CI) override {
//    llvm::errs() << "Plugin: BeginSourceFileAction called\n";
//
//    // 添加预处理器回调
//    Preprocessor &PP = CI.getPreprocessor();
//    PP.addPPCallbacks(std::make_unique<PthreadOncePPCallbacks>(CI, ShouldInsert));
//
//    return PluginASTAction::BeginSourceFileAction(CI);
//  }
//
//  void ExecuteAction() override {
//    llvm::errs() << "Plugin: ExecuteAction called\n";
//
//    // 调用基类实现
//    PluginASTAction::ExecuteAction();
//  }


private:
  bool ShouldInsert = false;
};

static FrontendPluginRegistry::Add<InsertPthreadOnceAction>
    X("insert-pthread-once2", "Insert pthread_once_t global variable");