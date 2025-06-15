#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Sema.h"
#include "llvm/ADT/StringRef.h"

using namespace clang;

namespace {

class PthreadOnceInserter {
public:
  PthreadOnceInserter(CompilerInstance &CI, bool ShouldInsert)
      : CI(CI), ShouldInsert(ShouldInsert) {}

  void Insert() {
    if (!ShouldInsert) return;

    // 确保Sema已经创建
    if (!CI.hasSema()) {
      llvm::errs() << "Error: Sema not available at insertion time\n";
      return;
    }

    // 插入头文件
    InsertHeader();

    // 插入全局变量
    InsertGlobalVar();
  }

private:
  void InsertHeader() {
    Preprocessor &PP = CI.getPreprocessor();
    SourceManager &SM = CI.getSourceManager();

    llvm::errs() << "InsertHeader\n";

    // 创建#include <pthread.h>指令
    std::string HeaderDirective = "#include <pthread.h>\n";
    std::unique_ptr<llvm::MemoryBuffer> Buffer =
        llvm::MemoryBuffer::getMemBufferCopy(HeaderDirective, "pthread_once_header");

    // 创建虚拟文件ID
    FileID PseudoFileID = SM.createFileID(
        std::move(Buffer),
        SrcMgr::C_User,
        /*LoadedID*/0, /*LoadedOffset*/0, SourceLocation()
    );

    // 添加到主文件之前
    SourceLocation IncludeLoc = SM.getLocForStartOfFile(SM.getMainFileID());
    PP.EnterSourceFile(PseudoFileID, /*DirLookup*/nullptr, IncludeLoc);
  }

  void InsertGlobalVar() {
    llvm::errs() << "InsertGlobalVar\n";

    ASTContext &Context = CI.getASTContext();
    Sema &S = CI.getSema();

    // 查找或创建pthread_once_t类型
    QualType PthreadOnceType = LookupPthreadOnceType(Context, S);
    if (PthreadOnceType.isNull()) return;

    // 创建全局变量声明
    IdentifierInfo *II = &Context.Idents.get("__pthread_once_global");
    TypeSourceInfo *TInfo = Context.getTrivialTypeSourceInfo(PthreadOnceType);
    VarDecl *VD = VarDecl::Create(
        Context,
        Context.getTranslationUnitDecl(),
        SourceLocation(),
        SourceLocation(),
        II,
        PthreadOnceType,
        TInfo,
        SC_Static
    );

    // 设置初始化为0
//    VD->setInit(Context.getNullPtr(PthreadOnceType));
    VD->setInit(createNullInitializer(Context, PthreadOnceType));

    // 添加到AST
    Context.getTranslationUnitDecl()->addDecl(VD);
//    Sema::DeclGroupPtrTy DG = Sema::DeclGroupPtrTy::make(DeclGroupRef(VD));
//    S.ActOnDeclarators(DG);
    // 使用Sema注册声明（兼容最新API）
    RegisterDeclWithSema(S, VD);
  }

  void RegisterDeclWithSema(Sema &S, VarDecl *VD) {
    // 最新Clang API兼容的方法
//    Sema::DeclGroupPtrTy DeclGroup = Sema::DeclGroupPtrTy::make(DeclGroupRef(VD));
    S.CurContext->addDecl(VD);

    // 如果Sema有当前作用域，使用它
    if (Scope *CurScope = S.getCurScope()) {
      if (CurScope->isDeclScope(VD)) {
        S.IdResolver.AddDecl(VD);
      }
    }

    // 标记声明为已添加
    VD->setAccess(AS_public);
  }

  // 创建空初始化器
  Expr *createNullInitializer(ASTContext &Context, QualType Ty) {
    // 对于指针类型，使用空指针常量
    if (Ty->isPointerType()) {
      return new (Context) ImplicitValueInitExpr(Ty);
    }

    // 对于结构体类型，创建零初始化
    if (const RecordType *RT = Ty->getAs<RecordType>()) {
      if (RecordDecl *RD = RT->getDecl()) {
        return new (Context) InitListExpr(Context, RD->getLocation(),
                                          std::nullopt, RD->getLocation());
      }
    }

    // 默认使用隐式值初始化
    return new (Context) ImplicitValueInitExpr(Ty);
  }

  QualType LookupPthreadOnceType(ASTContext &Context, Sema &S) {
    // 查找pthread_once_t类型声明
    DeclarationName Name = &Context.Idents.get("pthread_once_t");
    LookupResult R(S, Name, SourceLocation(), Sema::LookupOrdinaryName);

    if (!S.LookupName(R, S.TUScope)) {
      // 报告错误
      DiagnosticsEngine &DE = CI.getDiagnostics();
      unsigned DiagID = DE.getCustomDiagID(
          DiagnosticsEngine::Error,
          "pthread_once_t not found after including <pthread.h>"
      );
      DE.Report(SourceLocation(), DiagID);
      return QualType();
    }

    if (TypeDecl *TD = R.getAsSingle<TypeDecl>()) {
      return Context.getTypeDeclType(TD);
    }

    return QualType();
  }

  CompilerInstance &CI;
  bool ShouldInsert;
};

// 自定义ASTConsumer确保在正确时机执行
class PluginASTConsumer : public ASTConsumer {
public:
  PluginASTConsumer(CompilerInstance &CI, bool ShouldInsert)
      : CI(CI), ShouldInsert(ShouldInsert) {}

  void Initialize(ASTContext &Context) override {
    llvm::errs() << "Plugin: ASTConsumer::Initialize called\n";

    // 确保Sema已经创建
    if (!CI.hasSema()) {
      llvm::errs() << "Error: Sema not available in Initialize\n";
      return;
    }

    if (ShouldInsert) {
      llvm::errs() << "Plugin: Starting insertion process\n";
      PthreadOnceInserter Inserter(CI, ShouldInsert);
      Inserter.Insert();
    }
  }

private:
  CompilerInstance &CI;
  bool ShouldInsert;
};

class InsertPthreadOnceAction : public PluginASTAction {
protected:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(
      CompilerInstance &CI, llvm::StringRef) override {
    llvm::errs() << "Plugin: CreateASTConsumer called\n";
    return std::make_unique<PluginASTConsumer>(CI, ShouldInsert);
  }

  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &Args) override {
    llvm::errs() << "Plugin: ParseArgs called with " << Args.size() << " arguments\n";
//    for (const auto &Arg : Args) {
//      llvm::errs() << "Plugin: Argument: " << Arg << "\n";
//      if (Arg == "-insert_pthread_once_t") {
//        ShouldInsert = true;
//        llvm::errs() << "Plugin: insert_pthread_once_t flag detected\n";
//      }
//    }
    ShouldInsert = true;
    return true;
  }

  // 确保ExecuteAction被调用
  void ExecuteAction() override {
    llvm::errs() << "Plugin: ExecuteAction called\n";

    // 调用基类实现以确保ASTConsumer被创建
    PluginASTAction::ExecuteAction();
  }

  // 重写BeginSourceFileAction确保在正确时机执行
  bool BeginSourceFileAction(CompilerInstance &CI) override {
    llvm::errs() << "Plugin: BeginSourceFileAction called\n";
    return PluginASTAction::BeginSourceFileAction(CI);
  }

private:
  bool ShouldInsert = false;
};

} // namespace

static FrontendPluginRegistry::Add<InsertPthreadOnceAction>
    X("insert-pthread-once", "Insert pthread_once_t global variable");
