#include "FunctionChainPass.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/User.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <utility>

using namespace llvm;

llvm::cl::opt<bool> FunctionChainEnable("obffunctionchain", llvm::cl::init(true), llvm::cl::desc("Master Toggle"));

static constexpr unsigned CloneCap = 50;
static constexpr unsigned CascadeMaxRounds = 16;
static constexpr unsigned ThunkCap = 1024;
static constexpr bool EnableCascade = true;
static constexpr bool EnableThunkSalvage = true;
static constexpr bool EnableShapeRandomization = true;
static constexpr bool EnableBodyEncryption = true;
static constexpr bool EncConsts = true;
static constexpr bool EncStrings = true;
static constexpr bool EncGVPtrs = true;
static constexpr bool IndirectCallsEnabled = true;
static constexpr bool IndirectBranchesEnabled = true;

static constexpr uint64_t FNV1a64(const char* s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    while (*s)
    {
        h ^= (uint8_t)(*s);
        h *= 0x100000001b3ULL;
        ++s;
    }
    return h;
}

static uint64_t FNV1a64Range(StringRef s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    for (char c : s)
    {
        h ^= (uint8_t)c;
        h *= 0x100000001b3ULL;
    }
    return h;
}

static bool IsCRTSpecial(StringRef n)
{
    if (n.starts_with("_tls_callback")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("DllMain"):
        case FNV1a64("_DllMainCRTStartup"):
        case FNV1a64("DllMainCRTStartup"):
        case FNV1a64("mainCRTStartup"):
        case FNV1a64("wmainCRTStartup"):
        case FNV1a64("WinMainCRTStartup"):
        case FNV1a64("wWinMainCRTStartup"):
        case FNV1a64("_CRT_INIT"):
        case FNV1a64("__scrt_common_main"):
        case FNV1a64("__scrt_common_main_seh"):
        case FNV1a64("__scrt_dllmain_before_initialize_c"):
        case FNV1a64("__scrt_dllmain_after_initialize_c"):
            return true;
    }
    return false;
}

static bool IsCompilerHelper(StringRef n)
{
    if (n.starts_with("__GSHandlerCheck")) return true;
    if (n.starts_with("_RTC_")) return true;
    if (n.starts_with("__scrt_")) return true;
    if (n.starts_with("__acrt_")) return true;
    if (n.starts_with("__crt_")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("_chkstk"):
        case FNV1a64("__chkstk"):
        case FNV1a64("__chkstk_ms"):
        case FNV1a64("__security_check_cookie"):
        case FNV1a64("__security_init_cookie"):
        case FNV1a64("__CxxFrameHandler3"):
        case FNV1a64("__CxxFrameHandler4"):
        case FNV1a64("__C_specific_handler"):
        case FNV1a64("__CxxThrowException"):
        case FNV1a64("__std_terminate"):
        case FNV1a64("__std_exception_copy"):
        case FNV1a64("__std_exception_destroy"):
        case FNV1a64("__RTDynamicCast"):
        case FNV1a64("__RTtypeid"):
        case FNV1a64("__RTCastToVoid"):
        case FNV1a64("_purecall"):
        case FNV1a64("__purecall"):
        case FNV1a64("__report_rangecheckfailure"):
        case FNV1a64("__report_securityfailure"):
        case FNV1a64("_Init_thread_header"):
        case FNV1a64("_Init_thread_footer"):
        case FNV1a64("_Init_thread_abort"):
        case FNV1a64("_Init_thread_epoch"):
        case FNV1a64("__msvc_align"):
            return true;
    }
    return false;
}

static bool IsOurHelper(StringRef n)
{
    return n.starts_with("__fc_");
}

static bool IsMSVCHelperCallee(StringRef n)
{
    if (n.starts_with("__imp_")) return true;
    if (n.starts_with("__delayLoadHelper")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("__chkstk"):
        case FNV1a64("_alloca_probe"):
        case FNV1a64("__security_check_cookie"):
        case FNV1a64("__security_init_cookie"):
        case FNV1a64("__GSHandlerCheck"):
        case FNV1a64("__GSHandlerCheck_SEH"):
        case FNV1a64("__GSHandlerCheck_EH"):
        case FNV1a64("__CxxFrameHandler3"):
        case FNV1a64("__CxxFrameHandler4"):
        case FNV1a64("__C_specific_handler"):
        case FNV1a64("_setjmp"):
        case FNV1a64("_setjmp3"):
        case FNV1a64("longjmp"):
            return true;
    }
    return false;
}

static bool IsVTableGV(StringRef n)
{
    if (n.starts_with("??_7")) return true;
    if (n.starts_with("??_R4")) return true;
    if (n.starts_with("_ZTV")) return true;
    if (n.starts_with("_ZTC")) return true;
    if (n.starts_with("_ZTT")) return true;
    return false;
}

static void CollectGlobalCtorDtorFuncs(Module& m, DenseSet<Function*>& out)
{
    const StringRef tables[] = {"llvm.global_ctors", "llvm.global_dtors"};
    for (StringRef tn : tables)
    {
        GlobalVariable* gv = m.getNamedGlobal(tn);
        if (!gv || !gv->hasInitializer()) continue;
        auto* ca = dyn_cast<ConstantArray>(gv->getInitializer());
        if (!ca) continue;
        for (unsigned i = 0; i < ca->getNumOperands(); ++i)
        {
            auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
            if (!cs || cs->getNumOperands() < 2) continue;
            Value* v = cs->getOperand(1)->stripPointerCasts();
            if (auto* f = dyn_cast<Function>(v)) out.insert(f);
        }
    }
}

static void CollectFunctionsFromConstant(Constant* c, DenseSet<Function*>& out, DenseSet<Constant*>& visited)
{
    if (!c) return;
    if (!visited.insert(c).second) return;
    if (auto* f = dyn_cast<Function>(c)) { out.insert(f); return; }
    for (unsigned i = 0, n = c->getNumOperands(); i < n; ++i)
        if (auto* sub = dyn_cast<Constant>(c->getOperand(i)))
            CollectFunctionsFromConstant(sub, out, visited);
}

static void CollectVTableFuncs(Module& m, DenseSet<Function*>& out)
{
    DenseSet<Constant*> visited;
    for (GlobalVariable& gv : m.globals())
    {
        if (!gv.hasInitializer()) continue;
        if (!IsVTableGV(gv.getName())) continue;
        CollectFunctionsFromConstant(gv.getInitializer(), out, visited);
    }
}

static bool UserLeadsOnlyToMetadataGlobals(User* u, DenseSet<User*>& visited)
{
    if (!visited.insert(u).second) return true;
    if (auto* gv = dyn_cast<GlobalVariable>(u))
    {
        StringRef n = gv->getName();
        switch (FNV1a64Range(n))
        {
            case FNV1a64("llvm.global.annotations"):
            case FNV1a64("llvm.used"):
            case FNV1a64("llvm.compiler.used"):
            case FNV1a64("llvm.metadata"):
                return true;
        }
        return false;
    }
    if (isa<Instruction>(u)) return false;
    if (u->user_empty()) return false;
    for (User* uu : u->users())
        if (!UserLeadsOnlyToMetadataGlobals(uu, visited))
            return false;
    return true;
}

static bool DetectAddressTaken(Function& f)
{
    for (User* u : f.users())
    {
        if (auto* cb = dyn_cast<CallBase>(u))
        {
            if (cb->getCalledOperand() != &f) return true;
            continue;
        }
        DenseSet<User*> visited;
        if (!UserLeadsOnlyToMetadataGlobals(u, visited)) return true;
    }
    return false;
}

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;
        StringRef s = cds->getAsString();
        if (s.starts_with(tag) && s.size() == strlen(tag) + 1) return true;
    }
    return false;
}

static bool HasNoChainCryptAnnotation(Function& f)
{
    return HasAnnotationTag(f, "nochaincrypt");
}

static bool HasNoObfuscateAnnotation(Function& f)
{
    return HasAnnotationTag(f, "noobfus");
}

struct ClassifyResult
{
    bool eligible = false;
    bool sigmutable = false;
    bool addresstaken = false;
    bool haspersonality = false;
    bool hasinvokes = false;
    bool isvariadic = false;
};

static ClassifyResult ClassifyFunction(Function& f, const DenseSet<Function*>& ctordtorset)
{
    ClassifyResult r;
    if (f.isDeclaration() || f.isIntrinsic()) return r;
    StringRef name = f.getName();
    if (IsOurHelper(name)) return r;
    if (f.hasFnAttribute("fc-r6-thunk")) return r;
    if (f.hasFnAttribute(Attribute::Naked)) return r;
    if (IsCRTSpecial(name)) return r;
    if (IsCompilerHelper(name)) return r;
    if (ctordtorset.contains(&f)) return r;
    if (HasNoObfuscateAnnotation(f)) return r;
    if (HasNoChainCryptAnnotation(f)) return r;
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (isa<FuncletPadInst>(&i)) return r;
            if (isa<CatchReturnInst>(&i)) return r;
            if (isa<CleanupReturnInst>(&i)) return r;
            if (auto* ci = dyn_cast<CallInst>(&i))
                if (ci->isMustTailCall()) return r;
            if (isa<InvokeInst>(&i)) r.hasinvokes = true;
        }
    }
    r.isvariadic = f.isVarArg();
    r.addresstaken = DetectAddressTaken(f);
    r.haspersonality = f.hasPersonalityFn();
    r.eligible = true;
    r.sigmutable = !r.addresstaken && !r.haspersonality && !r.hasinvokes && !r.isvariadic;
    if (r.sigmutable)
    {
        for (User* u : f.users())
        {
            auto* cb = dyn_cast<CallBase>(u);
            if (!cb) continue;
            if (cb->getCalledOperand() != &f) continue;
            if (isa<InvokeInst>(cb) || isa<CallBrInst>(cb)) { r.sigmutable = false; break; }
        }
    }
    return r;
}

static uint64_t FCGen64()
{
    uint64_t a = (uint64_t)(rand() & 0xFFFF);
    uint64_t b = (uint64_t)(rand() & 0xFFFF);
    uint64_t c = (uint64_t)(rand() & 0xFFFF);
    uint64_t d = (uint64_t)(rand() & 0xFFFF);
    return a | (b << 16) | (c << 32) | (d << 48);
}

static unsigned CountCallInstXrefs(Function* f)
{
    unsigned n = 0;
    for (User* u : f->users())
    {
        auto* ci = dyn_cast<CallInst>(u);
        if (!ci) continue;
        if (ci->getCalledOperand() != f) continue;
        ++n;
    }
    return n;
}

static Function* CreateForwarderThunk(Function* g, unsigned idx)
{
    LLVMContext& c = g->getContext();
    Module* m = g->getParent();
    FunctionType* ft = g->getFunctionType();
    Function* t = Function::Create(ft, GlobalValue::InternalLinkage, g->getAddressSpace(), g->getName() + ".fct" + Twine(idx), m);
    t->copyAttributesFrom(g);
    t->setCallingConv(g->getCallingConv());
    t->setLinkage(GlobalValue::InternalLinkage);
    t->setUnnamedAddr(GlobalValue::UnnamedAddr::Local);
    if (t->hasPersonalityFn()) t->setPersonalityFn(nullptr);
    // thunk is tiny and tail call only; must pin NoInline so the inliner doesn't fold it back into its caller.
    t->addFnAttr(Attribute::NoInline);
    t->removeFnAttr(Attribute::AlwaysInline);
    t->removeFnAttr(Attribute::InlineHint);
    unsigned i = 0;
    for (Argument& a : t->args())
        a.setName(g->getArg(i++)->getName());
    BasicBlock* bb = BasicBlock::Create(c, "Entry", t);
    IRBuilder<> b(bb);
    SmallVector<Value*, 8> args;
    for (Argument& a : t->args()) args.push_back(&a);
    CallInst* fwd = b.CreateCall(g, args);
    fwd->setCallingConv(g->getCallingConv());
    fwd->setTailCall(true);
    if (g->getReturnType()->isVoidTy())
        b.CreateRetVoid();
    else
        b.CreateRet(fwd);
    return t;
}

static Function* CloneFunctionBody(Function* f, unsigned idx)
{
    Function* fi = Function::Create(f->getFunctionType(), f->getLinkage(), f->getAddressSpace(), f->getName() + ".fcc" + Twine(idx), f->getParent());
    fi->copyAttributesFrom(f);
    fi->setCallingConv(f->getCallingConv());
    ValueToValueMapTy vmap;
    auto oit = f->arg_begin();
    auto nit = fi->arg_begin();
    for (; oit != f->arg_end(); ++oit, ++nit)
    {
        nit->setName(oit->getName());
        vmap[&*oit] = &*nit;
    }
    SmallVector<ReturnInst*, 4> returns;
    CloneFunctionInto(fi, f, vmap, CloneFunctionChangeType::LocalChangesOnly, returns);
    return fi;
}

static Function* MutateSignature(Function* f)
{
    LLVMContext& c = f->getContext();
    FunctionType* oldft = f->getFunctionType();
    SmallVector<Type*, 8> newparams(oldft->params().begin(), oldft->params().end());
    newparams.push_back(Type::getInt64Ty(c));
    FunctionType* newft = FunctionType::get(oldft->getReturnType(), newparams, oldft->isVarArg());
    Function* fnew = Function::Create(newft, f->getLinkage(), f->getAddressSpace(), f->getName() + ".fc", f->getParent());
    fnew->copyAttributesFrom(f);
    fnew->setCallingConv(f->getCallingConv());
    ValueToValueMapTy vmap;
    auto oit = f->arg_begin();
    auto nit = fnew->arg_begin();
    for (; oit != f->arg_end(); ++oit, ++nit)
    {
        nit->setName(oit->getName());
        vmap[&*oit] = &*nit;
    }
    nit->setName("FCKIn");
    SmallVector<ReturnInst*, 4> returns;
    CloneFunctionInto(fnew, f, vmap, CloneFunctionChangeType::LocalChangesOnly, returns);
    fnew->addFnAttr("fc-sigmutated");
    // must pin NoInline on sig mutated callees; the inliner would collapse the K-pass-through CallBase into the caller's body
    fnew->addFnAttr(Attribute::NoInline);
    fnew->removeFnAttr(Attribute::AlwaysInline);
    fnew->removeFnAttr(Attribute::InlineHint);
    return fnew;
}

static void MarkChainInstr(Instruction* i)
{
    LLVMContext& c = i->getContext();
    i->setMetadata("fc.r1", MDNode::get(c, {}));
}

static AllocaInst* InjectPrologue(Function* fnew, uint64_t cf)
{
    LLVMContext& c = fnew->getContext();
    Type* i64 = Type::getInt64Ty(c);
    ArrayType* kslotty = ArrayType::get(i64, 2);
    BasicBlock& origentry = fnew->getEntryBlock();
    origentry.setName("FCOrigEntry");
    BasicBlock* fcentry = BasicBlock::Create(c, "FCPrologue", fnew, &origentry);
    IRBuilder<> b(fcentry);
    // alloca sized to 2 x i64 with 16-byte align keeps frame parity preserved AND reserves kslot[1] as volatile scratch for the shape scratch K write path
    AllocaInst* kslot = b.CreateAlloca(kslotty, nullptr, "FCKSlot");
    kslot->setAlignment(Align(16));
    Argument* kin = &*std::prev(fnew->arg_end());
    Value* k = b.CreateXor(kin, ConstantInt::get(i64, cf), "FCK");
    // store MUST be volatile; without it LLVM forwards the stored K through subsequent kslot loads and constant folds every body decryption back to plaintext at compile time
    b.CreateStore(k, kslot)->setVolatile(true);
    b.CreateBr(&origentry);
    return kslot;
}

static CallInst* RewriteCallsiteThreaded(CallInst* ci, Function* gnew, AllocaInst* callerkslot, uint64_t delta)
{
    LLVMContext& c = ci->getContext();
    IRBuilder<> b(ci);
    Type* i64 = Type::getInt64Ty(c);
    LoadInst* klive = b.CreateLoad(i64, callerkslot, "FCKLive");
    klive->setVolatile(true);
    MarkChainInstr(klive);
    unsigned shape = (EnableShapeRandomization && delta != 0) ? (FCGen64() & 1u) : 0;
    Value* kout = klive;
    if (delta != 0 && shape == 0)
    {
        Instruction* xori = cast<Instruction>(b.CreateXor(klive, ConstantInt::get(i64, delta), "FCKOut"));
        MarkChainInstr(xori);
        kout = xori;
    }
    else if (delta != 0 && shape == 1)
    {
        ArrayType* kslotty = ArrayType::get(i64, 2);
        uint64_t mask = FCGen64();
        uint64_t deltaadj = delta ^ mask;
        Instruction* xor1 = cast<Instruction>(b.CreateXor(klive, ConstantInt::get(i64, mask), "FCVolXor"));
        MarkChainInstr(xor1);
        Value* kslot1 = b.CreateConstInBoundsGEP2_32(kslotty, callerkslot, 0, 1, "FCVolScratch");
        auto* st = b.CreateAlignedStore(xor1, kslot1, Align(8));
        st->setVolatile(true);
        MarkChainInstr(st);
        LoadInst* reload = b.CreateAlignedLoad(i64, kslot1, Align(8), "FCVolReload");
        reload->setVolatile(true);
        MarkChainInstr(reload);
        Instruction* xor2 = cast<Instruction>(b.CreateXor(reload, ConstantInt::get(i64, deltaadj), "FCKOut"));
        MarkChainInstr(xor2);
        kout = xor2;
    }
    SmallVector<Value*, 8> newargs(ci->args().begin(), ci->args().end());
    newargs.push_back(kout);
    CallInst* newci = b.CreateCall(gnew->getFunctionType(), gnew, newargs);
    newci->setCallingConv(ci->getCallingConv());
    newci->setTailCallKind(ci->getTailCallKind());
    newci->setAttributes(ci->getAttributes());
    newci->setDebugLoc(ci->getDebugLoc());
    if (!ci->getType()->isVoidTy())
    {
        newci->takeName(ci);
        ci->replaceAllUsesWith(newci);
    }
    ci->eraseFromParent();
    return newci;
}

static CallInst* RewriteCallsiteBaked(CallInst* ci, Function* gnew, uint64_t kg, uint64_t cg)
{
    IRBuilder<> b(ci);
    Type* i64 = Type::getInt64Ty(ci->getContext());
    uint64_t kw = kg ^ cg;
    unsigned shape = EnableShapeRandomization ? (FCGen64() & 1u) : 0;
    Value* karg = nullptr;
    if (shape == 0)
    {
        karg = ConstantInt::get(i64, kw);
    }
    else
    {
        Module* m = ci->getModule();
        uint64_t gvrnd = FCGen64();
        uint64_t bakedadj = kw ^ gvrnd;
        // holder GV MUST be mutable (isConstant=false) or const-prop will fold the load back through the initializer and collapse to a literal, defeating the shape
        auto* gv = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, ConstantInt::get(i64, gvrnd), "__fc_bk_gv");
        gv->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
        Instruction* ld = b.CreateLoad(i64, gv, "FCBakedLoad");
        MarkChainInstr(ld);
        Instruction* xori = cast<Instruction>(b.CreateXor(ld, ConstantInt::get(i64, bakedadj), "FCBakedXor"));
        MarkChainInstr(xori);
        karg = xori;
    }
    SmallVector<Value*, 8> newargs(ci->args().begin(), ci->args().end());
    newargs.push_back(karg);
    CallInst* newci = b.CreateCall(gnew->getFunctionType(), gnew, newargs);
    newci->setCallingConv(ci->getCallingConv());
    newci->setTailCallKind(ci->getTailCallKind());
    newci->setAttributes(ci->getAttributes());
    newci->setDebugLoc(ci->getDebugLoc());
    if (!ci->getType()->isVoidTy())
    {
        newci->takeName(ci);
        ci->replaceAllUsesWith(newci);
    }
    ci->eraseFromParent();
    return newci;
}

struct EncryptContext
{
    Function* f = nullptr;
    uint64_t kf = 0;
    AllocaInst* kslot = nullptr;
    BasicBlock* origentry = nullptr;
    LoadInst* klive = nullptr;
    Value* klive32 = nullptr;
    Value* keydiff = nullptr;
    DenseSet<Instruction*> own;
};

static bool IsPrologueBB(const BasicBlock& bb)
{
    return bb.getName() == "FCPrologue";
}

static Function* ResolveCallee(CallBase* cb)
{
    if (Function* f = cb->getCalledFunction()) return f;
    Value* v = cb->getCalledOperand();
    if (!v) return nullptr;
    v = v->stripPointerCasts();
    for (unsigned i = 0; i < 8; ++i)
    {
        auto* ga = dyn_cast<GlobalAlias>(v);
        if (!ga) break;
        Constant* aliasee = ga->getAliasee();
        if (!aliasee) break;
        v = aliasee->stripPointerCasts();
    }
    return dyn_cast<Function>(v);
}

static bool SetupEncryptContext(EncryptContext& ctx)
{
    for (BasicBlock& bb : *ctx.f)
    {
        if (bb.getName() == "FCOrigEntry") { ctx.origentry = &bb; break; }
    }
    if (!ctx.origentry) return false;
    LLVMContext& c = ctx.f->getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    IRBuilder<> b(&ctx.origentry->front());
    ctx.klive = b.CreateLoad(i64, ctx.kslot, "FCK64");
    // load MUST be volatile; without it LLVM forward propagates the stored kf and constant folds every XOR/ADD decryption back to plaintext at compile time
    ctx.klive->setVolatile(true);
    ctx.own.insert(ctx.klive);
    Instruction* k32 = cast<Instruction>(b.CreateTrunc(ctx.klive, i32, "FCK32"));
    ctx.klive32 = k32;
    ctx.own.insert(k32);
    Instruction* kd = cast<Instruction>(b.CreateSub(ctx.klive, ConstantInt::get(i64, ctx.kf), "FCKeyDiff"));
    ctx.keydiff = kd;
    ctx.own.insert(kd);
    return true;
}

static bool IsEncryptableInstr(Instruction* i)
{
    if (i->getMetadata("fc.r1")) return false;
    if (isa<PHINode>(i)) return false;
    if (isa<GetElementPtrInst>(i)) return false;
    if (isa<SwitchInst>(i)) return false;
    if (isa<AllocaInst>(i)) return false;
    if (isa<ExtractValueInst>(i)) return false;
    if (isa<InsertValueInst>(i)) return false;
    if (isa<LandingPadInst>(i)) return false;
    if (isa<FuncletPadInst>(i)) return false;
    if (isa<CatchReturnInst>(i)) return false;
    if (isa<CleanupReturnInst>(i)) return false;
    if (isa<ResumeInst>(i)) return false;
    if (auto* cb = dyn_cast<CallBase>(i))
    {
        if (cb->isInlineAsm()) return false;
        if (cb->getIntrinsicID() != Intrinsic::not_intrinsic) return false;
    }
    return true;
}

static bool IsOperandData(Instruction* i, unsigned opidx)
{
    if (auto* cb = dyn_cast<CallBase>(i))
    {
        if (opidx >= cb->arg_size()) return false;
        if (cb->paramHasAttr(opidx, Attribute::ImmArg)) return false;
        // a sig mutated callee's trailing arg is the chain K write; encrypting it would XOR the baked K twice and break every downstream chain decryption
        Function* callee = ResolveCallee(cb);
        if (callee && callee->hasFnAttribute("fc-sigmutated") && opidx == cb->arg_size() - 1)
            return false;
        return true;
    }
    if (isa<StoreInst>(i))
    {
        if (opidx != 0) return false;
        return true;
    }
    if (isa<LoadInst>(i)) return false;
    if (isa<AtomicRMWInst>(i))
    {
        if (opidx != 1) return false;
        return true;
    }
    if (isa<AtomicCmpXchgInst>(i))
    {
        if (opidx != 1 && opidx != 2) return false;
        return true;
    }
    return true;
}

static void EncryptConstants(EncryptContext& ctx)
{
    LLVMContext& c = ctx.f->getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    SmallVector<std::pair<Instruction*, unsigned>, 32> targets;
    for (BasicBlock& bb : *ctx.f)
    {
        // the prologue BB holds the C_F XOR of the incoming K; its ConstantInt operand IS key material and must stay literal
        if (IsPrologueBB(bb)) continue;
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            if (i.getMetadata("fc.r1")) continue;
            if (!IsEncryptableInstr(&i)) continue;
            for (unsigned oi = 0, e = i.getNumOperands(); oi < e; ++oi)
            {
                auto* ci = dyn_cast<ConstantInt>(i.getOperand(oi));
                if (!ci) continue;
                unsigned bw = ci->getBitWidth();
                if (bw != 32 && bw != 64) continue;
                if (!IsOperandData(&i, oi)) continue;
                targets.push_back({&i, oi});
            }
        }
    }
    for (auto& t : targets)
    {
        Instruction* ins = t.first;
        unsigned opidx = t.second;
        auto* ci = cast<ConstantInt>(ins->getOperand(opidx));
        unsigned bw = ci->getBitWidth();
        IRBuilder<> b(ins);
        if (bw == 64)
        {
            uint64_t cv = ci->getZExtValue();
            uint64_t ciph = cv ^ ctx.kf;
            Instruction* dec = cast<Instruction>(b.CreateXor(ConstantInt::get(i64, ciph), ctx.klive, "FCDec"));
            ctx.own.insert(dec);
            ins->setOperand(opidx, dec);
        }
        else
        {
            uint32_t cv = (uint32_t)ci->getZExtValue();
            uint32_t ciph = cv ^ (uint32_t)(ctx.kf & 0xFFFFFFFFu);
            Instruction* dec = cast<Instruction>(b.CreateXor(ConstantInt::get(i32, ciph), ctx.klive32, "FCDec"));
            ctx.own.insert(dec);
            ins->setOperand(opidx, dec);
        }
    }
}

static void EncryptStrings(EncryptContext& ctx)
{
    DenseSet<GlobalVariable*> seen;
    SmallVector<GlobalVariable*, 16> entries;
    for (BasicBlock& bb : *ctx.f)
    {
        if (IsPrologueBB(bb)) continue;
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            if (i.getMetadata("fc.r1")) continue;
            for (unsigned oi = 0, oe = i.getNumOperands(); oi < oe; ++oi)
            {
                Value* op = i.getOperand(oi);
                Value* stripped = op;
                while (auto* gep = dyn_cast<GEPOperator>(stripped))
                    stripped = gep->getPointerOperand();
                auto* gv = dyn_cast<GlobalVariable>(stripped);
                if (!gv || !gv->isConstant() || !gv->hasInitializer()) continue;
                auto* arrt = dyn_cast<ArrayType>(gv->getValueType());
                if (!arrt) continue;
                Type* elemt = arrt->getElementType();
                if (!elemt->isIntegerTy(8) && !elemt->isIntegerTy(16)) continue;
                auto* init = dyn_cast<ConstantDataSequential>(gv->getInitializer());
                if (!init) continue;
                if (!seen.insert(gv).second) continue;
                entries.push_back(gv);
            }
        }
    }
    if (entries.empty()) return;
    LLVMContext& c = ctx.f->getContext();
    Type* i64 = Type::getInt64Ty(c);
    for (GlobalVariable* gv : entries)
    {
        auto* init = cast<ConstantDataSequential>(gv->getInitializer());
        auto* arrt = cast<ArrayType>(gv->getValueType());
        unsigned ebits = arrt->getElementType()->getIntegerBitWidth();
        unsigned esize = ebits / 8;
        unsigned nelems = init->getNumElements();
        unsigned total = nelems * esize;
        unsigned padded = ((total + 7) / 8) * 8;
        unsigned nchunks = padded / 8;
        unsigned elemsperchunk = 8 / esize;
        unsigned nchunksaligned = (nchunks + 1u) & ~1u;
        IRBuilder<> be(&ctx.f->getEntryBlock(), ctx.f->getEntryBlock().begin());
        AllocaInst* slot = be.CreateAlloca(i64, ConstantInt::get(i64, nchunksaligned), "FCStrBuf");
        slot->setAlignment(Align(16));
        ctx.own.insert(slot);
        Instruction* insertafter = cast<Instruction>(ctx.keydiff);
        IRBuilder<> bd(insertafter->getParent(), std::next(insertafter->getIterator()));
        for (unsigned chunkidx = 0; chunkidx < nchunks; ++chunkidx)
        {
            uint64_t plain = 0;
            for (unsigned k = 0; k < elemsperchunk; ++k)
            {
                unsigned elemidx = chunkidx * elemsperchunk + k;
                if (elemidx >= nelems) break;
                uint64_t v = init->getElementAsInteger(elemidx);
                plain |= v << (k * ebits);
            }
            uint64_t mask = FCGen64();
            uint64_t cipherct = plain + mask;
            Constant* cipherc = ConstantInt::get(i64, cipherct);
            Constant* maskc = ConstantInt::get(i64, mask);
            Value* effmask = bd.CreateAdd(maskc, ctx.keydiff, "FCStrEMask");
            Value* dec = bd.CreateSub(cipherc, effmask, "FCStrDec");
            Value* dst = bd.CreateGEP(i64, slot, ConstantInt::get(i64, chunkidx), "FCStrDst");
            Value* st = bd.CreateStore(dec, dst);
            if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
            if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
            if (auto* di = dyn_cast<Instruction>(dst)) ctx.own.insert(di);
            if (auto* di = dyn_cast<Instruction>(st)) ctx.own.insert(di);
        }
        SmallVector<Use*, 8> toreplace;
        for (Use& u : gv->uses())
        {
            auto* useri = dyn_cast<Instruction>(u.getUser());
            if (!useri) continue;
            if (useri->getFunction() != ctx.f) continue;
            if (ctx.own.contains(useri)) continue;
            toreplace.push_back(&u);
        }
        for (Use* u : toreplace) u->set(slot);
    }
}

static bool ShouldEncryptGVOperand(GlobalVariable* gv)
{
    if (!gv) return false;
    if (gv->getName().starts_with("llvm.")) return false;
    if (gv->getName().starts_with("__fc_")) return false;
    if (gv->getName().starts_with("__retcrypt_")) return false;
    if (gv->getName().starts_with("__tlscrypt_")) return false;
    if (gv->isThreadLocal()) return false;
    if (gv->isConstant() && gv->hasInitializer())
    {
        if (auto* arrt = dyn_cast<ArrayType>(gv->getValueType()))
        {
            Type* elemt = arrt->getElementType();
            if ((elemt->isIntegerTy(8) || elemt->isIntegerTy(16)) && isa<ConstantDataSequential>(gv->getInitializer()))
                return false;
        }
    }
    return true;
}

static void EncryptGVPtrs(EncryptContext& ctx)
{
    LLVMContext& c = ctx.f->getContext();
    Module* m = ctx.f->getParent();
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::getUnqual(c);
    DenseSet<GlobalVariable*> seen;
    SmallVector<GlobalVariable*, 16> gvs;
    for (BasicBlock& bb : *ctx.f)
    {
        if (IsPrologueBB(bb)) continue;
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            if (i.getMetadata("fc.r1")) continue;
            for (unsigned oi = 0, oe = i.getNumOperands(); oi < oe; ++oi)
            {
                auto* gv = dyn_cast<GlobalVariable>(i.getOperand(oi));
                if (!ShouldEncryptGVOperand(gv)) continue;
                if (!seen.insert(gv).second) continue;
                gvs.push_back(gv);
            }
        }
    }
    if (gvs.empty()) return;
    Instruction* insertafter = cast<Instruction>(ctx.keydiff);
    for (GlobalVariable* gv : gvs)
    {
        uint64_t mask = FCGen64();
        Constant* addr = ConstantExpr::getPtrToInt(gv, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);
        auto* holder = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__fc_gv_ref");
        holder->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
        IRBuilder<> b(insertafter->getParent(), std::next(insertafter->getIterator()));
        Value* loaded = b.CreateLoad(i64, holder, "FCGVLoad");
        Value* effmask = b.CreateAdd(maskc, ctx.keydiff, "FCGVEMask");
        Value* dec = b.CreateSub(loaded, effmask, "FCGVDec");
        Value* ptr = b.CreateIntToPtr(dec, ptrty, "FCGVP");
        if (auto* di = dyn_cast<Instruction>(loaded)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(ptr)) ctx.own.insert(di);
        SmallVector<Use*, 8> toreplace;
        for (Use& u : gv->uses())
        {
            auto* useri = dyn_cast<Instruction>(u.getUser());
            if (!useri) continue;
            if (useri->getFunction() != ctx.f) continue;
            if (ctx.own.contains(useri)) continue;
            toreplace.push_back(&u);
        }
        for (Use* u : toreplace) u->set(ptr);
        insertafter = cast<Instruction>(ptr);
    }
}

static void IndirectCalls(EncryptContext& ctx)
{
    LLVMContext& c = ctx.f->getContext();
    Module* m = ctx.f->getParent();
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::getUnqual(c);
    SmallVector<std::pair<CallBase*, Function*>, 32> toindirect;
    for (BasicBlock& bb : *ctx.f)
    {
        if (IsPrologueBB(bb)) continue;
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            if (i.getMetadata("fc.r1")) continue;
            auto* call = dyn_cast<CallBase>(&i);
            if (!call) continue;
            if (isa<CallBrInst>(call)) continue;
            if (call->isInlineAsm()) continue;
            if (auto* ci = dyn_cast<CallInst>(call))
                if (ci->isMustTailCall()) continue;
            Function* callee = ResolveCallee(call);
            if (!callee) continue;
            if (callee->isIntrinsic()) continue;
            StringRef name = callee->getName();
            if (name.starts_with("__fc_")) continue;
            if (name.starts_with("__tlscrypt_")) continue;
            if (name.starts_with("__retcrypt_")) continue;
            if (IsMSVCHelperCallee(name)) continue;
            // resolver may walk through a bitcast/alias chain whose declared type differs from the actual Function; indirecting against the original CallBase FunctionType would be a signature lie and break the call
            if (callee->getFunctionType() != call->getFunctionType()) continue;
            toindirect.push_back({call, callee});
        }
    }
    for (auto& e : toindirect)
    {
        CallBase* call = e.first;
        Function* callee = e.second;
        uint64_t mask = FCGen64();
        Constant* addr = ConstantExpr::getPtrToInt(callee, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);
        auto* gv = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__fc_ind_call");
        gv->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
        IRBuilder<> b(call);
        Value* loaded = b.CreateLoad(i64, gv, "FCCeeLoad");
        Value* effmask = b.CreateAdd(maskc, ctx.keydiff, "FCCeeEMask");
        Value* dec = b.CreateSub(loaded, effmask, "FCCeeDec");
        Value* fn = b.CreateIntToPtr(dec, ptrty, "FCCeeP");
        if (auto* di = dyn_cast<Instruction>(loaded)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(fn)) ctx.own.insert(di);
        call->setCalledOperand(fn);
    }
}

static void IndirectBranches(EncryptContext& ctx)
{
    LLVMContext& c = ctx.f->getContext();
    Module* m = ctx.f->getParent();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    PointerType* ptrty = PointerType::getUnqual(c);
    SmallVector<BranchInst*, 32> toindirect;
    DenseMap<BasicBlock*, unsigned> tgtidx;
    SmallVector<BasicBlock*, 32> tgtordered;
    for (BasicBlock& bb : *ctx.f)
    {
        if (IsPrologueBB(bb)) continue;
        auto* br = dyn_cast<BranchInst>(bb.getTerminator());
        if (!br) continue;
        if (ctx.own.contains(br)) continue;
        if (br->getMetadata("fc.r1")) continue;
        bool hasehsucc = false;
        for (BasicBlock* succ : br->successors())
            if (succ && succ->isEHPad()) { hasehsucc = true; break; }
        if (hasehsucc) continue;
        toindirect.push_back(br);
        for (BasicBlock* succ : br->successors())
            if (tgtidx.insert({succ, (unsigned)tgtordered.size()}).second)
                tgtordered.push_back(succ);
    }
    if (toindirect.empty()) return;
    unsigned n = tgtordered.size();
    ArrayType* at = ArrayType::get(i64, n);
    SmallVector<Constant*, 32> addrentries(n);
    SmallVector<Constant*, 32> maskentries(n);
    for (unsigned i = 0; i < n; ++i)
    {
        uint64_t mask = FCGen64();
        Constant* ba = BlockAddress::get(ctx.f, tgtordered[i]);
        Constant* baint = ConstantExpr::getPtrToInt(ba, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        addrentries[i] = ConstantExpr::getAdd(baint, maskc);
        maskentries[i] = maskc;
    }
    auto* addrtable = new GlobalVariable(*m, at, false, GlobalValue::PrivateLinkage, ConstantArray::get(at, addrentries), "__fc_ind_br_addrtbl");
    addrtable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    auto* masktable = new GlobalVariable(*m, at, false, GlobalValue::PrivateLinkage, ConstantArray::get(at, maskentries), "__fc_ind_br_masktbl");
    masktable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    Constant* zero32 = ConstantInt::get(i32, 0);
    for (BranchInst* br : toindirect)
    {
        IRBuilder<> b(br);
        Value* idx;
        if (br->isConditional())
        {
            Constant* idxt = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
            Constant* idxf = ConstantInt::get(i32, tgtidx[br->getSuccessor(1)]);
            idx = b.CreateSelect(br->getCondition(), idxt, idxf, "FCBrIdx");
        }
        else
        {
            idx = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
        }
        Value* agep = b.CreateGEP(at, addrtable, {zero32, idx}, "FCBrAGep");
        Value* mgep = b.CreateGEP(at, masktable, {zero32, idx}, "FCBrMGep");
        Value* loaded = b.CreateLoad(i64, agep, "FCBrLoad");
        Value* mask = b.CreateLoad(i64, mgep, "FCBrMask");
        Value* effmask = b.CreateAdd(mask, ctx.keydiff, "FCBrEMask");
        Value* dec = b.CreateSub(loaded, effmask, "FCBrDec");
        Value* tgt = b.CreateIntToPtr(dec, ptrty, "FCBrP");
        if (auto* di = dyn_cast<Instruction>(idx)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(agep)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(mgep)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(loaded)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(mask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(tgt)) ctx.own.insert(di);
        SmallVector<BasicBlock*, 2> succs;
        for (BasicBlock* sc : br->successors()) succs.push_back(sc);
        auto* ibr = IndirectBrInst::Create(tgt, succs.size(), br);
        for (BasicBlock* sc : succs) ibr->addDestination(sc);
        ibr->copyMetadata(*br);
        ctx.own.insert(ibr);
        br->eraseFromParent();
    }
}

static void EncryptBody(Function* fnew, uint64_t kf, AllocaInst* kslot)
{
    EncryptContext ctx;
    ctx.f = fnew;
    ctx.kf = kf;
    ctx.kslot = kslot;
    if (!SetupEncryptContext(ctx)) return;
    if (EncConsts) EncryptConstants(ctx);
    if (EncStrings) EncryptStrings(ctx);
    if (EncGVPtrs) EncryptGVPtrs(ctx);
    if (IndirectCallsEnabled) IndirectCalls(ctx);
    if (IndirectBranchesEnabled) IndirectBranches(ctx);
}

bool RunFunctionChain(Module& m)
{
    if (!FunctionChainEnable) return false;
    DenseSet<Function*> ctordtorset;
    CollectGlobalCtorDtorFuncs(m, ctordtorset);
    DenseSet<Function*> vtableset;
    CollectVTableFuncs(m, vtableset);
    DenseSet<Function*> eligibleset;
    DenseSet<Function*> sigmutable;
    for (Function& f : m)
    {
        ClassifyResult r = ClassifyFunction(f, ctordtorset);
        if (!r.eligible) continue;
        eligibleset.insert(&f);
        if (r.sigmutable) sigmutable.insert(&f);
    }
    DenseSet<Function*> live(eligibleset.begin(), eligibleset.end());
    const unsigned maxrounds = EnableCascade ? CascadeMaxRounds : 1u;
    for (unsigned round = 1; round <= maxrounds; ++round)
    {
        unsigned clonedthisround = 0;
        SmallVector<Function*, 1024> snap(sigmutable.begin(), sigmutable.end());
        for (Function* f : snap)
        {
            if (!live.count(f)) continue;
            SmallVector<CallInst*, 4> xrefs;
            for (User* u : f->users())
            {
                auto* ci = dyn_cast<CallInst>(u);
                if (!ci) continue;
                if (ci->getCalledOperand() != f) continue;
                xrefs.push_back(ci);
            }
            if (xrefs.empty()) continue;
            if (xrefs.size() == 1) continue;
            if (xrefs.size() > (size_t)CloneCap) continue;
            for (unsigned i = 0; i < xrefs.size(); ++i)
            {
                Function* fi = CloneFunctionBody(f, i);
                xrefs[i]->setCalledOperand(fi);
                live.insert(fi);
                sigmutable.insert(fi);
                ++clonedthisround;
            }
            live.erase(f);
            sigmutable.erase(f);
            if (f->use_empty()) f->eraseFromParent();
        }
        if (clonedthisround == 0) break;
    }
    if (EnableCascade && EnableThunkSalvage)
    {
        SmallVector<Function*, 128> stillmulti;
        for (Function* f : sigmutable)
            if (live.count(f) && CountCallInstXrefs(f) > 1)
                stillmulti.push_back(f);
        for (Function* g : stillmulti)
        {
            SmallVector<CallInst*, 32> xrefs;
            for (User* u : g->users())
            {
                auto* ci = dyn_cast<CallInst>(u);
                if (!ci) continue;
                if (ci->getCalledOperand() != g) continue;
                xrefs.push_back(ci);
            }
            if (xrefs.size() < 2) continue;
            if (xrefs.size() > (size_t)ThunkCap)
            {
                sigmutable.erase(g);
                continue;
            }
            for (unsigned i = 0; i < xrefs.size(); ++i)
            {
                Function* t = CreateForwarderThunk(g, i);
                xrefs[i]->setCalledOperand(t);
                live.insert(t);
                sigmutable.insert(t);
            }
            sigmutable.erase(g);
        }
    }
    DenseMap<Function*, Function*> sigmap;
    DenseMap<Function*, uint64_t> kmap;
    DenseMap<Function*, uint64_t> cmap;
    DenseMap<Function*, AllocaInst*> kslots;
    DenseSet<Function*> doomed;
    DenseSet<Function*> surviving;
    {
        SmallVector<Function*, 1024> snap(live.begin(), live.end());
        for (Function* f : snap)
        {
            if (!sigmutable.count(f)) continue;
            if (CountCallInstXrefs(f) != 1) continue;
            Function* fnew = MutateSignature(f);
            sigmap[f] = fnew;
            kmap[fnew] = FCGen64();
            cmap[fnew] = FCGen64();
            doomed.insert(f);
            surviving.insert(fnew);
        }
    }
    for (auto& kv : sigmap)
    {
        Function* fnew = kv.second;
        uint64_t cf = cmap.lookup(fnew);
        kslots[fnew] = InjectPrologue(fnew, cf);
    }
    for (auto& kv : sigmap)
    {
        Function* fold = kv.first;
        Function* fnew = kv.second;
        SmallVector<CallInst*, 4> torewrite;
        for (User* u : fold->users())
        {
            auto* ci = dyn_cast<CallInst>(u);
            if (!ci) continue;
            if (ci->getCalledOperand() != fold) continue;
            Function* container = ci->getFunction();
            if (doomed.count(container)) continue;
            torewrite.push_back(ci);
        }
        uint64_t kf = kmap.lookup(fnew);
        uint64_t cf = cmap.lookup(fnew);
        for (CallInst* ci : torewrite)
        {
            Function* container = ci->getFunction();
            if (surviving.count(container))
            {
                uint64_t kp = kmap.lookup(container);
                uint64_t delta = kp ^ kf ^ cf;
                RewriteCallsiteThreaded(ci, fnew, kslots.lookup(container), delta);
            }
            else
            {
                RewriteCallsiteBaked(ci, fnew, kf, cf);
            }
        }
    }
    for (auto& kv : sigmap)
    {
        Function* fold = kv.first;
        Function* fnew = kv.second;
        bool stuck = false;
        for (User* u : fold->users())
        {
            if (auto* cb = dyn_cast<CallBase>(u))
            {
                if (cb->getCalledOperand() == fold && !doomed.count(cb->getFunction()))
                {
                    stuck = true;
                    break;
                }
            }
        }
        if (stuck) continue;
        if (!fold->use_empty()) fold->replaceAllUsesWith(fnew);
        fold->eraseFromParent();
    }
    if (EnableBodyEncryption)
    {
        for (auto& kv : sigmap)
        {
            Function* fnew = kv.second;
            uint64_t kf = kmap.lookup(fnew);
            AllocaInst* kslot = kslots.lookup(fnew);
            if (!kslot) continue;
            EncryptBody(fnew, kf, kslot);
        }
    }
    return !sigmap.empty();
}

PreservedAnalyses FunctionChainPass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunFunctionChain(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}