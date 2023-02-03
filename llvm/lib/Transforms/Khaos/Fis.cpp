//===- Fis.cpp ------------------------------------- ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//
//
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Khaos/KhaosCodeExtractor.h"
#include "llvm/Transforms/Khaos/Utils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <string>

#define DEBUG_TYPE "fis"

static cl::opt<bool> fisInline("fis-inline", cl::init(true), cl::Hidden,
                               cl::desc("Inline extracted function"));

#define FISCONSIZE 16
#define FISCONHALFSIZE (FISCONSIZE >> 1)

namespace {
struct Fis : public ModulePass {
  static char ID;
  Fis() : ModulePass(ID) {
    initializeFisPass(*PassRegistry::getPassRegistry());
  }
  vector<Function *> colFuncs(Module &M);
  void colSuccBBs(BasicBlock &BB,
                  SmallSetVector<BasicBlock *, FISCONHALFSIZE> &BBCands,
                  SmallSetVector<BasicBlock *, FISCONSIZE> &BBAll);
  bool runOnModule(Module &M) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequiredID(LoopSimplifyID);
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
  }
private:
    SmallVector<SmallVector<BasicBlock *, FISCONSIZE>, FISCONSIZE> regs;
    SmallSetVector<BasicBlock *, FISCONHALFSIZE> BBCands;
    SmallSetVector<BasicBlock *, FISCONSIZE> BBAll;
    SmallSetVector<BasicBlock *, FISCONSIZE> freqBBSet;
    SmallSetVector<BasicBlock *, FISCONSIZE> regBBs;
    BlockFrequency freqBBThresold;
    BasicBlock *fisEnBB;
public:
    uint64_t BBCnt;
    uint64_t extractedFuncNum;
};
} // namespace

vector<Function *> Fis::colFuncs(Module &M) {
  vector<Function *> Funcs;
  for (auto i = M.begin(); i != M.end(); i++) {
    Function *F = &(*i);
    if (F->isKhaosFunction() || F->getName().startswith("std") ||
        F->isIntrinsic() || F->isDeclaration() || F->empty() ||
        F->hasOptNone() || F->getName().contains("INS_6VectorIdEEE5solveIN"))
      continue;
    Funcs.push_back(F);
  }
  return Funcs;
}

void Fis::colSuccBBs(BasicBlock &BB,
                     SmallSetVector<BasicBlock *, FISCONHALFSIZE> &BBCands,
                     SmallSetVector<BasicBlock *, FISCONSIZE> &BBAll) {
  succ_iterator SI = succ_begin(&BB), SE = succ_end(&BB);
BEGIN:
  if (SI == SE)
    goto RET;
  if (BBAll.insert(*SI) && BBCands.insert(*SI))
    BBCnt++;
  SI++;
  goto BEGIN;
RET:
  return;
}

bool Fis::runOnModule(Module &M) {
  bool MC = false;
  vector<Function *> Funcs = colFuncs(M);
  SmallSetVector<Function *, FISCONSIZE> exFu;
  for (Function *F : Funcs) {
    bool exFl = false;
    regs.clear();
    BBAll.clear();
    BBCands.clear();
    freqBBSet.clear();
    fisEnBB = nullptr;
    BlockFrequencyInfo &BBFreq =
        getAnalysis<BlockFrequencyInfoWrapperPass>(*F).getBFI();
    DominatorTree DT(*F);
    LoopInfo LI{DT};
    BasicBlock &origEnBB = F->getEntryBlock();
    freqBBThresold = BBFreq.getEntryFreq();

    BBAll.insert(&origEnBB);
    colSuccBBs(origEnBB, BBCands, BBAll);
    for (BasicBlock &BB : *F)
      (LI.getLoopFor(&BB) == nullptr)
          ? ((BBFreq.getBlockFreq(&BB) >= freqBBThresold)
                 ? (!isa<SwitchInst>(BB.getTerminator()) ? freqBBSet.insert(&BB)
                                                         : false)
                 : false)
          : false;
  BUILDREG:
    if (BBCands.empty())
      goto EXTRACTREGHEAD;
    fisEnBB = BBCands.pop_back_val();
    if (freqBBSet.count(fisEnBB)) {
      colSuccBBs(*fisEnBB, BBCands, BBAll);
      goto BUILDREG;
    }
    regBBs.clear();
    regBBs.insert(fisEnBB);
    {
      auto depFirstIt = ++df_begin(fisEnBB), depFirstEnd = df_end(fisEnBB);
      BasicBlock *BB = nullptr;
    DEPFIRSTDOMCHECK:
      if (depFirstEnd == depFirstIt)
        goto DEPFIRSTDOMCHECKEND;
      BB = *depFirstIt;
      if (!DT.dominates(fisEnBB, BB)) {
        if (BBAll.insert(BB) && BBCands.insert(BB))
          BBCnt++;
        depFirstIt.skipChildren();
      DEPFIRSTDOMCHECKTRAMPOLINE:
        goto DEPFIRSTDOMCHECK;
      }
      regBBs.insert(BB);
      ++depFirstIt;
      goto DEPFIRSTDOMCHECKTRAMPOLINE;
    DEPFIRSTDOMCHECKEND:;
    }

    for (auto &BBIt : regBBs) {
      if (BBIt->getLandingPadInst() == nullptr)
        continue;
      if (BBIt->getLandingPadInst()->isCleanup() &&
          BBIt->getLandingPadInst()->getNumClauses() > (FISCONSIZE >> 4))
        goto BUILDREG;
    }
    {
      SmallVector<BasicBlock *, FISCONSIZE> newReg(regBBs.begin(),
                                                   regBBs.end());
      regs.push_back(newReg);
    }
    goto BUILDREG;

  EXTRACTREGHEAD:
    auto regIt = regs.begin(), regEnd = regs.end();
    uint ONL = 0;
    Function *CHF = nullptr;
  EXTRACTREG:
    if (regIt == regEnd)
      goto RECORDEXTRACTEDFUNC;
    if (regIt->size() <= 0)
      goto EXTRACTNEXTREG;
    ONL = (*regIt)[0]->getParent()->getName().size();
    if ((CHF = KhaosExtractor(*regIt).extractCodeRegion()) == nullptr)
      goto EXTRACTNEXTREG;
    CHF->setKhaosFunction(true);
    assert(ONL > 0 && "how can the name of a function is empty?");
    CHF->setONL(ONL);
    exFl |= true;
  EXTRACTNEXTREG:
    regIt++;
    goto EXTRACTREG;
  RECORDEXTRACTEDFUNC:
    if (exFl && exFu.insert(F)) extractedFuncNum++;
    MC |= exFl;
  } // outtest for end

  if (!fisInline)
    goto END;
  {
    auto FI = exFu.begin(), FE = exFu.end();
    SmallSetVector<CallSite, FISCONSIZE> Calls;
  FISINLINE:
    if (FI == FE)
      goto END;
    Calls.clear();
    if ((*FI)->getBasicBlockList().size() > (FISCONSIZE + (FISCONSIZE >> 2)) ||
        (*FI)->hasFnAttribute(Attribute::NoInline) || !isInlineViable(**FI))
      goto FISINLINENEXT;
    for (User *U : (*FI)->users())
      if (auto CS = CallSite(U))
        CS.getCalledFunction() == (*FI)
            ? ((CS.getParent()->getParent() != (*FI)) ? Calls.insert(CS)
                                                      : false)
            : false;
    for (CallSite CS : Calls) {
      llvm::InlineFunctionInfo IFI;
      MC |= InlineFunction(CS, IFI);
    }
  FISINLINENEXT:
    FI++;
    goto FISINLINE;
  }

END:
  return MC;
}

char Fis::ID = 0;

INITIALIZE_PASS_BEGIN(Fis, "fisPass", "Fis Pass", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopSimplify)
INITIALIZE_PASS_DEPENDENCY(BlockFrequencyInfoWrapperPass)
INITIALIZE_PASS_END(Fis, "fisPass", "Fis Pass", false, false)

ModulePass *llvm::createFisPass() { return new Fis(); }
