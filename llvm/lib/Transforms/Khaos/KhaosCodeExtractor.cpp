//===- KhaosCodeExtractor.cpp ----------------------------- ---------------===//
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
#include "llvm/Transforms/Khaos/KhaosCodeExtractor.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BlockFrequencyInfoImpl.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Pass.h"
#include "llvm/Support/BlockFrequency.h"
#include "llvm/Support/BranchProbability.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include <cassert>
#include <cstdint>
#include <iterator>
#include <map>
#include <set>
#include <utility>
#include <vector>

using namespace llvm;
using namespace llvm::PatternMatch;
using ProfileCount = Function::ProfileCount;

#define DEBUG_TYPE "khaos-extractor"

static cl::opt<bool> AggrArgsOpt("khaos-aggregate-extracted-args", cl::Hidden,
                                 cl::desc(""));

static bool isBBVal4Ex(const BasicBlock &BB,
                       const SetVector<BasicBlock *> &Result, bool AllowVarArgs,
                       bool AllowAlloca) {
  if (BB.hasAddressTaken())
    return false;

  SmallPtrSet<User const *, 16> Visited;
  SmallVector<User const *, 16> ToVisit;

  for (Instruction const &Inst : BB)
    ToVisit.push_back(&Inst);

  while (!ToVisit.empty()) {
    User const *Curr = ToVisit.pop_back_val();
    if (!Visited.insert(Curr).second)
      continue;
    if (isa<BlockAddress const>(Curr))
      return false;

    if (isa<Instruction>(Curr) && cast<Instruction>(Curr)->getParent() != &BB)
      continue;

    for (auto const &U : Curr->operands()) {
      if (auto *UU = dyn_cast<User>(U))
        ToVisit.push_back(UU);
    }
  }

  for (BasicBlock::const_iterator I = BB.begin(), E = BB.end(); I != E; ++I) {
    if (isa<AllocaInst>(I)) {
      if (!AllowAlloca)
        return false;
      continue;
    }

    if (const auto *II = dyn_cast<InvokeInst>(I)) {
      if (auto *UBB = II->getUnwindDest())
        if (!Result.count(UBB))
          return false;
      continue;
    }

    if (const auto *CSI = dyn_cast<CatchSwitchInst>(I)) {
      if (auto *UBB = CSI->getUnwindDest())
        if (!Result.count(UBB))
          return false;
      for (auto *HBB : CSI->handlers())
        if (!Result.count(const_cast<BasicBlock *>(HBB)))
          return false;
      continue;
    }

    if (const auto *CPI = dyn_cast<CatchPadInst>(I)) {
      for (const auto *U : CPI->users())
        if (const auto *CRI = dyn_cast<CatchReturnInst>(U))
          if (!Result.count(const_cast<BasicBlock *>(CRI->getParent())))
            return false;
      continue;
    }

    if (const auto *CPI = dyn_cast<CleanupPadInst>(I)) {
      for (const auto *U : CPI->users())
        if (const auto *CRI = dyn_cast<CleanupReturnInst>(U))
          if (!Result.count(const_cast<BasicBlock *>(CRI->getParent())))
            return false;
      continue;
    }
    if (const auto *CRI = dyn_cast<CleanupReturnInst>(I)) {
      if (auto *UBB = CRI->getUnwindDest())
        if (!Result.count(UBB))
          return false;
      continue;
    }

    if (const CallInst *CI = dyn_cast<CallInst>(I)) {
      if (const Function *F = CI->getCalledFunction()) {
        auto IID = F->getIntrinsicID();
        if (IID == Intrinsic::vastart) {
          if (AllowVarArgs)
            continue;
          else
            return false;
        }

        if (IID == Intrinsic::eh_typeid_for)
          return false;
      }
    }
  }

  return true;
}

SmallVector<Type *, 8>
KhaosExtractor::getValTypes(const ValueSet &inputs) const {
  SmallVector<Type *, 8> VT;
  for (const Value *Arg : inputs) {
    VT.push_back(Arg->getType());
  }
  return VT;
}

static SetVector<BasicBlock *>
buildExtractionBlockSet(ArrayRef<BasicBlock *> BBs, DominatorTree *DT,
                        bool AllowVarArgs, bool AllowAlloca) {
  assert(!BBs.empty() && "The set of blocks to extract must be non-empty");
  SetVector<BasicBlock *> Result;

  for (BasicBlock *BB : BBs) {
    if (DT && !DT->isReachableFromEntry(BB))
      continue;

    if (!Result.insert(BB))
      llvm_unreachable("Repeated basic blocks in extraction input");
  }

  LLVM_DEBUG(dbgs() << "Region front block: " << Result.front()->getName()
                    << '\n');

  for (auto *BB : Result) {
    if (!isBBVal4Ex(*BB, Result, AllowVarArgs, AllowAlloca))
      return {};

    if (BB == Result.front()) {
      if (BB->isEHPad()) {
        LLVM_DEBUG(dbgs() << "The first block cannot be an unwind block\n");
        return {};
      }
      continue;
    }

    for (auto *PBB : predecessors(BB))
      if (!Result.count(PBB)) {
        LLVM_DEBUG(dbgs() << "No blocks in this region may have entries from "
                             "outside the region except for the first block!\n"
                          << "Problematic source BB: " << BB->getName() << "\n"
                          << "Problematic destination BB: " << PBB->getName()
                          << "\n");
        return {};
      }
  }

  return Result;
}

KhaosExtractor::KhaosExtractor(ArrayRef<BasicBlock *> BBs, DominatorTree *DT,
                               bool AggregateArgs, BlockFrequencyInfo *BFI,
                               BranchProbabilityInfo *BPI, AssumptionCache *AC,
                               bool AllowVarArgs, bool AllowAlloca,
                               std::string Suffix)
    : DT(DT), AggregateArgs(AggregateArgs || AggrArgsOpt), BFI(BFI), BPI(BPI),
      AC(AC), AlVariableArgs(AllowVarArgs),
      Blocks(buildExtractionBlockSet(BBs, DT, AllowVarArgs, AllowAlloca)),
      Suffix(Suffix) {}

KhaosExtractor::KhaosExtractor(DominatorTree &DT, Loop &L, bool AggregateArgs,
                               BlockFrequencyInfo *BFI,
                               BranchProbabilityInfo *BPI, AssumptionCache *AC,
                               std::string Suffix)
    : DT(&DT), AggregateArgs(AggregateArgs || AggrArgsOpt), BFI(BFI), BPI(BPI),
      AC(AC), AlVariableArgs(false),
      Blocks(buildExtractionBlockSet(L.getBlocks(), &DT, false, false)),
      Suffix(Suffix) {}

static bool definedInRegion(const SetVector<BasicBlock *> &Blocks, Value *V) {
  if (Instruction *I = dyn_cast<Instruction>(V))
    if (Blocks.count(I->getParent()))
      return true;
  return false;
}

static bool definedInCaller(const SetVector<BasicBlock *> &Blocks, Value *V) {
  if (isa<Argument>(V))
    return true;
  if (Instruction *I = dyn_cast<Instruction>(V))
    if (!Blocks.count(I->getParent()))
      return true;
  return false;
}

static BasicBlock *getCommonExitBlock(const SetVector<BasicBlock *> &Blocks) {
  BasicBlock *CommonExitBlock = nullptr;
  auto hasNonCommonExitSucc = [&](BasicBlock *Block) {
    for (auto *Succ : successors(Block)) {
      if (Blocks.count(Succ))
        continue;
      if (!CommonExitBlock) {
        CommonExitBlock = Succ;
        continue;
      }
      if (CommonExitBlock == Succ)
        continue;

      return true;
    }
    return false;
  };

  if (any_of(Blocks, hasNonCommonExitSucc))
    return nullptr;

  return CommonExitBlock;
}

bool KhaosExtractor::isLegalToShrinkwrapLifetimeMarkers(
    Instruction *Addr) const {
  AllocaInst *AI = cast<AllocaInst>(Addr->stripInBoundsConstantOffsets());
  Function *Func = (*Blocks.begin())->getParent();
  for (BasicBlock &BB : *Func) {
    if (Blocks.count(&BB))
      continue;
    for (Instruction &II : BB) {
      if (isa<DbgInfoIntrinsic>(II))
        continue;

      unsigned Opcode = II.getOpcode();
      Value *MemAddr = nullptr;
      switch (Opcode) {
      case Instruction::Store:
      case Instruction::Load: {
        if (Opcode == Instruction::Store) {
          StoreInst *SI = cast<StoreInst>(&II);
          MemAddr = SI->getPointerOperand();
        } else {
          LoadInst *LI = cast<LoadInst>(&II);
          MemAddr = LI->getPointerOperand();
        }
        if (dyn_cast<Constant>(MemAddr))
          break;
        Value *Base = MemAddr->stripInBoundsConstantOffsets();
        if (!isa<AllocaInst>(Base) || Base == AI)
          return false;
        break;
      }
      default: {
        IntrinsicInst *IntrInst = dyn_cast<IntrinsicInst>(&II);
        if (IntrInst) {
          if (IntrInst->isLifetimeStartOrEnd())
            break;
          return false;
        }
        if (II.mayHaveSideEffects())
          return false;
      }
      }
    }
  }

  return true;
}

BasicBlock *
KhaosExtractor::findOrCreateBlockForHoisting(BasicBlock *CommonExitBlock) {
  BasicBlock *SinglePredFromOutlineRegion = nullptr;
  assert(!Blocks.count(CommonExitBlock) &&
         "Expect a block outside the region!");
  for (auto *Pred : predecessors(CommonExitBlock)) {
    if (!Blocks.count(Pred))
      continue;
    if (!SinglePredFromOutlineRegion) {
      SinglePredFromOutlineRegion = Pred;
    } else if (SinglePredFromOutlineRegion != Pred) {
      SinglePredFromOutlineRegion = nullptr;
      break;
    }
  }

  if (SinglePredFromOutlineRegion)
    return SinglePredFromOutlineRegion;

#ifndef NDEBUG
  auto getFirstPHI = [](BasicBlock *BB) {
    BasicBlock::iterator I = BB->begin();
    PHINode *FirstPhi = nullptr;
    while (I != BB->end()) {
      PHINode *Phi = dyn_cast<PHINode>(I);
      if (!Phi)
        break;
      if (!FirstPhi) {
        FirstPhi = Phi;
        break;
      }
    }
    return FirstPhi;
  };
  assert(!getFirstPHI(CommonExitBlock) && "Phi not expected");
#endif

  BasicBlock *NewExitBlock = CommonExitBlock->splitBasicBlock(
      CommonExitBlock->getFirstNonPHI()->getIterator());

  for (auto PI = pred_begin(CommonExitBlock), PE = pred_end(CommonExitBlock);
       PI != PE;) {
    BasicBlock *Pred = *PI++;
    if (Blocks.count(Pred))
      continue;
    Pred->getTerminator()->replaceUsesOfWith(CommonExitBlock, NewExitBlock);
  }
  Blocks.insert(CommonExitBlock);
  return CommonExitBlock;
}

KhaosExtractor::LifetimeMarkerInfo
KhaosExtractor::getLifetimeMarkers(Instruction *Addr,
                                   BasicBlock *ExitBlock) const {
  LifetimeMarkerInfo Info;

  for (User *U : Addr->users()) {
    IntrinsicInst *IntrInst = dyn_cast<IntrinsicInst>(U);
    if (IntrInst) {
      if (IntrInst->getIntrinsicID() == Intrinsic::lifetime_start) {
        if (Info.LifeStart)
          return {};
        Info.LifeStart = IntrInst;
      }
      if (IntrInst->getIntrinsicID() == Intrinsic::lifetime_end) {
        if (Info.LifeEnd)
          return {};
        Info.LifeEnd = IntrInst;
      }
      continue;
    }
    if (!definedInRegion(Blocks, U))
      return {};
  }

  if (!Info.LifeStart || !Info.LifeEnd)
    return {};

  Info.SinkLifeStart = !definedInRegion(Blocks, Info.LifeStart);
  Info.HoistLifeEnd = !definedInRegion(Blocks, Info.LifeEnd);
  if ((Info.SinkLifeStart || Info.HoistLifeEnd) &&
      !isLegalToShrinkwrapLifetimeMarkers(Addr))
    return {};

  if (Info.HoistLifeEnd && !ExitBlock)
    return {};

  return Info;
}

void KhaosExtractor::findAllocas(ValueSet &SinkCands, ValueSet &HoistCands,
                                 BasicBlock *&ExitBlock) const {
  Function *Func = (*Blocks.begin())->getParent();
  ExitBlock = getCommonExitBlock(Blocks);

  auto moveOrIgnoreLifetimeMarkers =
      [&](const LifetimeMarkerInfo &LMI) -> bool {
    if (!LMI.LifeStart)
      return false;
    if (LMI.SinkLifeStart) {
      LLVM_DEBUG(dbgs() << "Sinking lifetime.start: " << *LMI.LifeStart
                        << "\n");
      SinkCands.insert(LMI.LifeStart);
    }
    if (LMI.HoistLifeEnd) {
      LLVM_DEBUG(dbgs() << "Hoisting lifetime.end: " << *LMI.LifeEnd << "\n");
      HoistCands.insert(LMI.LifeEnd);
    }
    return true;
  };

  for (BasicBlock &BB : *Func) {
    if (Blocks.count(&BB))
      continue;
    for (Instruction &II : BB) {
      auto *AI = dyn_cast<AllocaInst>(&II);
      if (!AI)
        continue;

      LifetimeMarkerInfo MarkerInfo = getLifetimeMarkers(AI, ExitBlock);
      bool Moved = moveOrIgnoreLifetimeMarkers(MarkerInfo);
      if (Moved) {
        LLVM_DEBUG(dbgs() << "Sinking alloca: " << *AI << "\n");
        SinkCands.insert(AI);
        continue;
      }

      SmallVector<Instruction *, 2> Bitcasts;
      SmallVector<LifetimeMarkerInfo, 2> BitcastLifetimeInfo;
      for (User *U : AI->users()) {
        if (U->stripInBoundsConstantOffsets() == AI) {
          Instruction *Bitcast = cast<Instruction>(U);
          LifetimeMarkerInfo LMI = getLifetimeMarkers(Bitcast, ExitBlock);
          if (LMI.LifeStart) {
            Bitcasts.push_back(Bitcast);
            BitcastLifetimeInfo.push_back(LMI);
            continue;
          }
        }

        if (!definedInRegion(Blocks, U)) {
          Bitcasts.clear();
          break;
        }
      }

      if (Bitcasts.empty())
        continue;

      LLVM_DEBUG(dbgs() << "Sinking alloca (via bitcast): " << *AI << "\n");
      SinkCands.insert(AI);
      for (unsigned I = 0, E = Bitcasts.size(); I != E; ++I) {
        Instruction *BitcastAddr = Bitcasts[I];
        const LifetimeMarkerInfo &LMI = BitcastLifetimeInfo[I];
        assert(LMI.LifeStart &&
               "Unsafe to sink bitcast without lifetime markers");
        moveOrIgnoreLifetimeMarkers(LMI);
        if (!definedInRegion(Blocks, BitcastAddr)) {
          LLVM_DEBUG(dbgs()
                     << "Sinking bitcast-of-alloca: " << *BitcastAddr << "\n");
          SinkCands.insert(BitcastAddr);
        }
      }
    }
  }
}

void KhaosExtractor::DFDep(ValueSet &ins, ValueSet &outs, const ValueSet &sinks,
                           bool InsO) const {
  for (BasicBlock *BB : Blocks) {
    for (Instruction &II : *BB) {
      for (User::op_iterator OI = II.op_begin(), OE = II.op_end(); OI != OE;
           ++OI) {
        Value *V = *OI;
        if (!sinks.count(V) && definedInCaller(Blocks, V))
          ins.insert(V);
      }

      if (InsO)
        return;

      for (User *U : II.users())
        if (!definedInRegion(Blocks, U)) {
          outs.insert(&II);
          break;
        }
    }
  }
}

void KhaosExtractor::severSplitPHINodesOfEntry(BasicBlock *&Header) {
  unsigned NumPredsFromRegion = 0;
  unsigned NumPredsOutsideRegion = 0;

  if (Header != &Header->getParent()->getEntryBlock()) {
    PHINode *PN = dyn_cast<PHINode>(Header->begin());
    if (!PN)
      return;

    for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i)
      if (Blocks.count(PN->getIncomingBlock(i)))
        ++NumPredsFromRegion;
      else
        ++NumPredsOutsideRegion;

    if (NumPredsOutsideRegion <= 1)
      return;
  }

  BasicBlock *NewBB = SplitBlock(Header, Header->getFirstNonPHI(), DT);

  BasicBlock *OldPred = Header;
  Blocks.remove(OldPred);
  Blocks.insert(NewBB);
  Header = NewBB;

  if (NumPredsFromRegion) {
    PHINode *PN = cast<PHINode>(OldPred->begin());
    for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i)
      if (Blocks.count(PN->getIncomingBlock(i))) {
        Instruction *TI = PN->getIncomingBlock(i)->getTerminator();
        TI->replaceUsesOfWith(OldPred, NewBB);
      }

    BasicBlock::iterator AfterPHIs;
    for (AfterPHIs = OldPred->begin(); isa<PHINode>(AfterPHIs); ++AfterPHIs) {
      PHINode *PN = cast<PHINode>(AfterPHIs);
      PHINode *NewPN = PHINode::Create(PN->getType(), 1 + NumPredsFromRegion,
                                       PN->getName() + ".ce", &NewBB->front());
      PN->replaceAllUsesWith(NewPN);
      NewPN->addIncoming(PN, OldPred);

      for (unsigned i = 0; i != PN->getNumIncomingValues(); ++i) {
        if (Blocks.count(PN->getIncomingBlock(i))) {
          NewPN->addIncoming(PN->getIncomingValue(i), PN->getIncomingBlock(i));
          PN->removeIncomingValue(i);
          --i;
        }
      }
    }
  }
}

bool KhaosExtractor::checkArgs(const ValueSet &ins) const {
  if (Blocks.empty())
    return false;
  Function *F = (*Blocks.begin())->getParent();
  SmallVector<Type *, 8> VT = getValTypes(ins);
  for (auto it : VT) {
    switch (it->getTypeID()) {
    case Type::TypeID::VoidTyID:
    case Type::TypeID::FunctionTyID:
    case Type::TypeID::TokenTyID:
    case Type::TypeID::MetadataTyID:
      return false;
    default:;
    }
  }

  if (AlVariableArgs && F->getFunctionType()->isVarArg()) {
    auto it = F->begin(), end = F->end();
    BasicBlock *BB = nullptr;
  CEHCKVARRGS:
    if (it == end)
      goto CEHCKVARRGSEND;
    BB = &(*it);
    if (Blocks.count(BB))
      goto CEHCKVARRGSNEXT;
    {
      auto ii = BB->begin(), ie = BB->end();
      while (ii != ie) {
        if (const CallInst *CI = dyn_cast<CallInst>(ii++))
          if (const Function *callee = CI->getCalledFunction())
            if (callee->getIntrinsicID() == Intrinsic::vastart ||
                callee->getIntrinsicID() == Intrinsic::vaend)
              return false;
      }
    }
  CEHCKVARRGSNEXT:
    it++;
    goto CEHCKVARRGS;
  CEHCKVARRGSEND:;
  }

  return true;
}

AllocaInst *KhaosExtractor::fEscAlloc(CallInst *CI) {
  ConstantInt *CINT = dyn_cast<ConstantInt>(CI->getOperand(2));
  int AlIdx = CINT->getSExtValue();
  Function *CF = dyn_cast<Function>(CI->getOperand(0)->stripPointerCasts());
  BasicBlock &CFEntryBB = CF->getEntryBlock();
  for (Instruction &CFI : CFEntryBB) {
    if (CallInst *CFCI = dyn_cast<CallInst>(&CFI)) {
      Function *LE = CFCI->getCalledFunction();
      if (LE && LE->getIntrinsicID() == Intrinsic::localescape) {
        AllocaInst *CFAI = dyn_cast<AllocaInst>(CFCI->getOperand(AlIdx));
        return CFAI;
      }
    }
  }

  return nullptr;
}

void KhaosExtractor::severSplitPHINodesOfExits(
    const SmallPtrSetImpl<BasicBlock *> &Exits) {
  for (BasicBlock *ExitBB : Exits) {
    BasicBlock *NewBB = nullptr;

    for (PHINode &PN : ExitBB->phis()) {
      SmallVector<unsigned, 2> IncomingVals;
      for (unsigned i = 0; i < PN.getNumIncomingValues(); ++i)
        if (Blocks.count(PN.getIncomingBlock(i)))
          IncomingVals.push_back(i);

      if (IncomingVals.size() <= 1)
        continue;

      if (!NewBB) {
        NewBB = BasicBlock::Create(ExitBB->getContext(),
                                   ExitBB->getName() + ".split",
                                   ExitBB->getParent(), ExitBB);
        SmallVector<BasicBlock *, 4> Preds(pred_begin(ExitBB),
                                           pred_end(ExitBB));
        for (BasicBlock *PredBB : Preds)
          if (Blocks.count(PredBB))
            PredBB->getTerminator()->replaceUsesOfWith(ExitBB, NewBB);
        BranchInst::Create(ExitBB, NewBB);
        Blocks.insert(NewBB);
      }

      PHINode *NewPN =
          PHINode::Create(PN.getType(), IncomingVals.size(),
                          PN.getName() + ".ce", NewBB->getFirstNonPHI());
      for (unsigned i : IncomingVals)
        NewPN->addIncoming(PN.getIncomingValue(i), PN.getIncomingBlock(i));
      for (unsigned i : reverse(IncomingVals))
        PN.removeIncomingValue(i, false);
      PN.addIncoming(NewPN, NewBB);
    }
  }
}

void KhaosExtractor::splitReturnBlocks() {
  for (BasicBlock *Block : Blocks)
    if (ReturnInst *RI = dyn_cast<ReturnInst>(Block->getTerminator())) {
      BasicBlock *New =
          Block->splitBasicBlock(RI->getIterator(), Block->getName() + ".ret");
      if (DT) {
        DomTreeNode *OldNode = DT->getNode(Block);
        SmallVector<DomTreeNode *, 8> Children(OldNode->begin(),
                                               OldNode->end());

        DomTreeNode *NewNode = DT->addNewBlock(New, Block);

        for (DomTreeNode *I : Children)
          DT->changeImmediateDominator(I, NewNode);
      }
    }
}

Function *KhaosExtractor::constructFunction(ValueSet &inputs, ValueSet &outputs,
                                            BasicBlock *header,
                                            BasicBlock *newRootNode,
                                            BasicBlock *newHeader,
                                            Function *oldFunction, Module *M) {
  LLVM_DEBUG(dbgs() << "inputs: " << inputs.size() << "\n");
  LLVM_DEBUG(dbgs() << "outputs: " << outputs.size() << "\n");

  switch (NumExitBlocks) {
  case 0:
  case 1:
    RetTy = Type::getVoidTy(header->getContext());
    break;
  case 2:
    RetTy = Type::getInt1Ty(header->getContext());
    break;
  default:
    RetTy = Type::getInt16Ty(header->getContext());
    break;
  }

  std::vector<Type *> paramTy;

  LLVMContext &Con = M->getContext();
  SmallVector<CatchPadInst *, 8> CPIV;
  SmallVector<CallInst *, 8> LRCIV;
  SmallVector<CallInst *, 8> RFCIV;

  fCPI(CPIV);
  fLRIAndRFP(CPIV, LRCIV, RFCIV);

  int cntRF = RFCIV.size();
  int cntLR = LRCIV.size();

  for (int i = 0; i < cntLR; i++) {
    CallInst *LRI = LRCIV[i];
    AllocaInst *alloca = fEscAlloc(LRI);
    assert(alloca != nullptr &&
           "Cannot find the alloca according to localrecover correctly");
    LoadInst *load = new LoadInst(alloca, "FasA");
    newHeader->getInstList().push_back(load);
    Value *V = dyn_cast<Value>(load);
    inputs.insert(V);
  }

  for (Value *value : inputs) {
    LLVM_DEBUG(dbgs() << "value used in func: " << *value << "\n");
    paramTy.push_back(value->getType());
  }

  for (Value *output : outputs) {
    LLVM_DEBUG(dbgs() << "instr used in func: " << *output << "\n");
    if (AggregateArgs)
      paramTy.push_back(output->getType());
    else
      paramTy.push_back(PointerType::getUnqual(output->getType()));
  }

  LLVM_DEBUG({
    dbgs() << "Function type: " << *RetTy << " f(";
    for (Type *i : paramTy)
      dbgs() << *i << ", ";
    dbgs() << ")\n";
  });

  StructType *StructTy;
  if (AggregateArgs && (inputs.size() + outputs.size() > 0)) {
    StructTy = StructType::get(M->getContext(), paramTy);
    paramTy.clear();
    paramTy.push_back(PointerType::getUnqual(StructTy));
  }
  FunctionType *funcType = FunctionType::get(
      RetTy, paramTy, AlVariableArgs && oldFunction->isVarArg());

  std::string SuffixToUse =
      Suffix.empty()
          ? (header->getName().empty() ? "extracted" : header->getName().str())
          : Suffix;
  std::string oldFunctionName = oldFunction->getName().str();

  std::string oldVal1 = ".";
  std::string oldVal2 = "-";
  const std::string newVal = "_";
  while (true) {
    std::string::size_type pos(0);
    if ((pos = oldFunctionName.find(oldVal1)) != std::string::npos) {
      oldFunctionName.replace(pos, oldVal1.length(), newVal);
    } else
      break;
  }
  while (true) {
    std::string::size_type pos(0);
    if ((pos = oldFunctionName.find(oldVal2)) != std::string::npos) {
      oldFunctionName.replace(pos, oldVal2.length(), newVal);
    } else
      break;
  }
  while (true) {
    std::string::size_type pos(0);
    if ((pos = SuffixToUse.find(oldVal1)) != std::string::npos) {
      SuffixToUse.replace(pos, oldVal1.length(), newVal);
    } else
      break;
  }
  while (true) {
    std::string::size_type pos(0);
    if ((pos = SuffixToUse.find(oldVal2)) != std::string::npos) {
      SuffixToUse.replace(pos, oldVal2.length(), newVal);
    } else
      break;
  }

  Function *newFunction = Function::Create(
      funcType, GlobalValue::InternalLinkage, oldFunction->getAddressSpace(),
      oldFunctionName + "_" + SuffixToUse, M);
  if (oldFunction->doesNotThrow())
    newFunction->setDoesNotThrow();

  if (oldFunction->hasUWTable())
    newFunction->setHasUWTable();

  for (const auto &Attr : oldFunction->getAttributes().getFnAttributes()) {
    if (Attr.isStringAttribute()) {
      if (Attr.getKindAsString() == "thunk")
        continue;
    } else
      switch (Attr.getKindAsEnum()) {
      case Attribute::Alignment:
      case Attribute::AllocSize:
      case Attribute::ArgMemOnly:
      case Attribute::Builtin:
      case Attribute::ByVal:
      case Attribute::Convergent:
      case Attribute::Dereferenceable:
      case Attribute::DereferenceableOrNull:
      case Attribute::InAlloca:
      case Attribute::InReg:
      case Attribute::InaccessibleMemOnly:
      case Attribute::InaccessibleMemOrArgMemOnly:
      case Attribute::JumpTable:
      case Attribute::Naked:
      case Attribute::Nest:
      case Attribute::NoAlias:
      case Attribute::NoBuiltin:
      case Attribute::NoCapture:
      case Attribute::NoReturn:
      case Attribute::NoSync:
      case Attribute::None:
      case Attribute::NonNull:
      case Attribute::ReadNone:
      case Attribute::ReadOnly:
      case Attribute::Returned:
      case Attribute::ReturnsTwice:
      case Attribute::SExt:
      case Attribute::Speculatable:
      case Attribute::StackAlignment:
      case Attribute::StructRet:
      case Attribute::SwiftError:
      case Attribute::SwiftSelf:
      case Attribute::WillReturn:
      case Attribute::WriteOnly:
      case Attribute::ZExt:
      case Attribute::ImmArg:
      case Attribute::EndAttrKinds:
        continue;
      case Attribute::AlwaysInline:
      case Attribute::Cold:
      case Attribute::NoRecurse:
      case Attribute::InlineHint:
      case Attribute::MinSize:
      case Attribute::NoDuplicate:
      case Attribute::NoFree:
      case Attribute::NoImplicitFloat:
      case Attribute::NoInline:
      case Attribute::NonLazyBind:
      case Attribute::NoRedZone:
      case Attribute::NoUnwind:
      case Attribute::OptForFuzzing:
      case Attribute::OptimizeNone:
      case Attribute::OptimizeForSize:
      case Attribute::SafeStack:
      case Attribute::ShadowCallStack:
      case Attribute::SanitizeAddress:
      case Attribute::SanitizeMemory:
      case Attribute::SanitizeThread:
      case Attribute::SanitizeHWAddress:
      case Attribute::SanitizeMemTag:
      case Attribute::SpeculativeLoadHardening:
      case Attribute::StackProtect:
      case Attribute::StackProtectReq:
      case Attribute::StackProtectStrong:
      case Attribute::StrictFP:
      case Attribute::UWTable:
      case Attribute::NoCfCheck:
        break;
      }

    newFunction->addFnAttr(Attr);
  }

  if (cntLR) {
    Instruction *Rootbr = &(newRootNode->getInstList().back());

    std::vector<Value *> AforLE;
    std::vector<Value *> FasAVec;
    for (int i = 0; i < cntLR; i++) {
      Value *FasAinNewF =
          &*(newFunction->arg_begin() + newFunction->arg_size() - cntLR + i);
      Type *FasATy = FasAinNewF->getType();
      AllocaInst *RootAl = new AllocaInst(
          FasATy, M->getDataLayout().getAllocaAddrSpace(), "", Rootbr);
      RootAl->setAlignment(8);
      FasAVec.push_back(FasAinNewF);
      AforLE.push_back(RootAl);
    }

    for (int i = 0; i < AforLE.size(); i++) {
      StoreInst *storeInRoot =
          new StoreInst(FasAVec[i], AforLE[i], false, Rootbr);
    }

    ArrayRef<Value *> AforLEArr(AforLE);

    Function *LEFn =
        llvm::Intrinsic::getDeclaration(M, llvm::Intrinsic::localescape);
    CallInst *callInRoot = CallInst::Create(LEFn, AforLEArr, "", Rootbr);
  }

  newFunction->getBasicBlockList().push_back(newRootNode);

  Function::arg_iterator AI = newFunction->arg_begin();

  for (unsigned i = 0, e = inputs.size(); i != e; ++i) {
    Value *RewriteVal;
    if (AggregateArgs) {
      Value *Idx[2];
      Idx[0] = Constant::getNullValue(Type::getInt32Ty(header->getContext()));
      Idx[1] = ConstantInt::get(Type::getInt32Ty(header->getContext()), i);
      Instruction *TI = newFunction->begin()->getTerminator();
      GetElementPtrInst *GEP = GetElementPtrInst::Create(
          StructTy, &*AI, Idx, "gep_" + inputs[i]->getName(), TI);
      RewriteVal = new LoadInst(StructTy->getElementType(i), GEP,
                                "loadgep_" + inputs[i]->getName(), TI);
    } else
      RewriteVal = &*AI++;

    std::vector<User *> Users(inputs[i]->user_begin(), inputs[i]->user_end());
    for (User *use : Users)
      if (Instruction *inst = dyn_cast<Instruction>(use))
        if (Blocks.count(inst->getParent()))
          inst->replaceUsesOfWith(inputs[i], RewriteVal);
  }

  if (!AggregateArgs) {
    AI = newFunction->arg_begin();
    for (unsigned i = 0, e = inputs.size(); i != e; ++i, ++AI)
      AI->setName(inputs[i]->getName());
    for (unsigned i = 0, e = outputs.size(); i != e; ++i, ++AI)
      AI->setName(outputs[i]->getName() + ".out");
  }

  std::vector<User *> Users(header->user_begin(), header->user_end());
  for (unsigned i = 0, e = Users.size(); i != e; ++i)
    if (Instruction *I = dyn_cast<Instruction>(Users[i]))
      if (I->isTerminator() && !Blocks.count(I->getParent()) &&
          I->getParent()->getParent() == oldFunction)
        I->replaceUsesOfWith(header, newHeader);

  Constant *PI8Fn =
      ConstantExpr::getBitCast(newFunction, Type::getInt8PtrTy(Con));
  for (int i = 0; i < cntRF; i++) {
    CallInst *RFP = RFCIV[i];
    RFP->setOperand(0, PI8Fn);
  }
  for (int i = 0; i < cntLR; i++) {
    CallInst *LRI = LRCIV[i];
    LRI->setOperand(0, PI8Fn);
    LRI->setOperand(2, ConstantInt::get(Type::getInt32Ty(Con), i));
  }

  return newFunction;
}

static void eraseLifetimeMarkersOnInputs(const SetVector<BasicBlock *> &Blocks,
                                         const SetVector<Value *> &SunkAllocas,
                                         SetVector<Value *> &LifetimesStart) {
  for (BasicBlock *BB : Blocks) {
    for (auto It = BB->begin(), End = BB->end(); It != End;) {
      auto *II = dyn_cast<IntrinsicInst>(&*It);
      ++It;
      if (!II || !II->isLifetimeStartOrEnd())
        continue;

      Value *Mem = II->getOperand(1)->stripInBoundsOffsets();
      if (SunkAllocas.count(Mem) || definedInRegion(Blocks, Mem))
        continue;

      if (II->getIntrinsicID() == Intrinsic::lifetime_start)
        LifetimesStart.insert(Mem);
      II->eraseFromParent();
    }
  }
}

void KhaosExtractor::fLRIAndRFP(SmallVector<CatchPadInst *, 8> &CPIvec,
                                SmallVector<CallInst *, 8> &LRIvec,
                                SmallVector<CallInst *, 8> &RFPvec) {
  while (!CPIvec.empty()) {
    CatchPadInst *cpi = CPIvec.back();
    CPIvec.pop_back();

    int numOfLRI = 0;
    int numOfRFP = 0;
    Value *A = cpi->getArgOperand(0);
    Function *FF = dyn_cast<Function>(A->stripPointerCasts());
    for (BasicBlock &FBB : *FF) {
      for (Instruction &FI : FBB) {
        if (CallInst *CI = dyn_cast<CallInst>(&FI)) {
          if (const Function *IF = CI->getCalledFunction()) {
            auto IID = IF->getIntrinsicID();
            if (IID == Intrinsic::eh_recoverfp) {
              RFPvec.push_back(CI);
              numOfRFP++;
            } else if (IID == Intrinsic::localrecover) {
              LRIvec.push_back(CI);
              numOfLRI++;
            }
          }
        }
      }
    }

    assert((numOfRFP == 0 && numOfLRI == 0) ||
           (numOfRFP == 1 && numOfLRI >= 1) &&
               "The num of recover.fp and localrecover is not correct");
  }
}

static void insertLifetimeMarkersSurroundingCall(
    Module *M, ArrayRef<Value *> LifetimesStart, ArrayRef<Value *> LifetimesEnd,
    CallInst *TheCall) {
  LLVMContext &Ctx = M->getContext();
  auto Int8PtrTy = Type::getInt8PtrTy(Ctx);
  auto NegativeOne = ConstantInt::getSigned(Type::getInt64Ty(Ctx), -1);
  Instruction *Term = TheCall->getParent()->getTerminator();

  DenseMap<Value *, Value *> Bitcasts;

  auto insertMarkers = [&](Function *MarkerFunc, ArrayRef<Value *> Objects,
                           bool InsertBefore) {
    for (Value *Mem : Objects) {
      assert((!isa<Instruction>(Mem) || cast<Instruction>(Mem)->getFunction() ==
                                            TheCall->getFunction()) &&
             "Input memory not defined in original function");
      Value *&MemAsI8Ptr = Bitcasts[Mem];
      if (!MemAsI8Ptr) {
        if (Mem->getType() == Int8PtrTy)
          MemAsI8Ptr = Mem;
        else
          MemAsI8Ptr =
              CastInst::CreatePointerCast(Mem, Int8PtrTy, "lt.cast", TheCall);
      }

      auto Marker = CallInst::Create(MarkerFunc, {NegativeOne, MemAsI8Ptr});
      if (InsertBefore)
        Marker->insertBefore(TheCall);
      else
        Marker->insertBefore(Term);
    }
  };

  if (!LifetimesStart.empty()) {
    auto StartFn = llvm::Intrinsic::getDeclaration(
        M, llvm::Intrinsic::lifetime_start, Int8PtrTy);
    insertMarkers(StartFn, LifetimesStart, true);
  }

  if (!LifetimesEnd.empty()) {
    auto EndFn = llvm::Intrinsic::getDeclaration(
        M, llvm::Intrinsic::lifetime_end, Int8PtrTy);
    insertMarkers(EndFn, LifetimesEnd, false);
  }
}

CallInst *KhaosExtractor::emitCallAndSwitchStatement(Function *newFunction,
                                                     BasicBlock *codeReplacer,
                                                     ValueSet &inputs,
                                                     ValueSet &outputs) {
  std::vector<Value *> params, StructValues, ReloadOutputs, Reloads;

  Module *M = newFunction->getParent();
  LLVMContext &Context = M->getContext();
  const DataLayout &DL = M->getDataLayout();
  CallInst *call = nullptr;

  unsigned ArgNo = 0;
  SmallVector<unsigned, 1> SwiftErrorArgs;
  for (Value *input : inputs) {
    if (AggregateArgs)
      StructValues.push_back(input);
    else {
      params.push_back(input);
      if (input->isSwiftError())
        SwiftErrorArgs.push_back(ArgNo);
    }
    ++ArgNo;
  }

  for (Value *output : outputs) {
    if (AggregateArgs) {
      StructValues.push_back(output);
    } else {
      AllocaInst *alloca =
          new AllocaInst(output->getType(), DL.getAllocaAddrSpace(), nullptr,
                         output->getName() + ".loc",
                         &codeReplacer->getParent()->front().front());
      ReloadOutputs.push_back(alloca);
      params.push_back(alloca);
    }
  }

  StructType *StructArgTy = nullptr;
  AllocaInst *Struct = nullptr;
  if (AggregateArgs && (inputs.size() + outputs.size() > 0)) {
    std::vector<Type *> ArgTypes;
    for (ValueSet::iterator v = StructValues.begin(), ve = StructValues.end();
         v != ve; ++v)
      ArgTypes.push_back((*v)->getType());

    StructArgTy = StructType::get(newFunction->getContext(), ArgTypes);
    Struct = new AllocaInst(StructArgTy, DL.getAllocaAddrSpace(), nullptr,
                            "structArg",
                            &codeReplacer->getParent()->front().front());
    params.push_back(Struct);

    for (unsigned i = 0, e = inputs.size(); i != e; ++i) {
      Value *Idx[2];
      Idx[0] = Constant::getNullValue(Type::getInt32Ty(Context));
      Idx[1] = ConstantInt::get(Type::getInt32Ty(Context), i);
      GetElementPtrInst *GEP = GetElementPtrInst::Create(
          StructArgTy, Struct, Idx, "gep_" + StructValues[i]->getName());
      codeReplacer->getInstList().push_back(GEP);
      StoreInst *SI = new StoreInst(StructValues[i], GEP);
      codeReplacer->getInstList().push_back(SI);
    }
  }

  call = CallInst::Create(newFunction, params,
                          NumExitBlocks > 1 ? "targetBlock" : "");
  if (codeReplacer->getParent()->getSubprogram()) {
    if (auto DL = newFunction->getEntryBlock().getTerminator()->getDebugLoc())
      call->setDebugLoc(DL);
  }
  codeReplacer->getInstList().push_back(call);

  for (unsigned SwiftErrArgNo : SwiftErrorArgs) {
    call->addParamAttr(SwiftErrArgNo, Attribute::SwiftError);
    newFunction->addParamAttr(SwiftErrArgNo, Attribute::SwiftError);
  }

  Function::arg_iterator OutputArgBegin = newFunction->arg_begin();
  unsigned FirstOut = inputs.size();
  if (!AggregateArgs)
    std::advance(OutputArgBegin, inputs.size());

  for (unsigned i = 0, e = outputs.size(); i != e; ++i) {
    Value *Output = nullptr;
    if (AggregateArgs) {
      Value *Idx[2];
      Idx[0] = Constant::getNullValue(Type::getInt32Ty(Context));
      Idx[1] = ConstantInt::get(Type::getInt32Ty(Context), FirstOut + i);
      GetElementPtrInst *GEP = GetElementPtrInst::Create(
          StructArgTy, Struct, Idx, "gep_reload_" + outputs[i]->getName());
      codeReplacer->getInstList().push_back(GEP);
      Output = GEP;
    } else {
      Output = ReloadOutputs[i];
    }
    LoadInst *load = new LoadInst(outputs[i]->getType(), Output,
                                  outputs[i]->getName() + ".reload");
    Reloads.push_back(load);
    codeReplacer->getInstList().push_back(load);
    std::vector<User *> Users(outputs[i]->user_begin(), outputs[i]->user_end());
    for (unsigned u = 0, e = Users.size(); u != e; ++u) {
      Instruction *inst = cast<Instruction>(Users[u]);
      if (!Blocks.count(inst->getParent()))
        inst->replaceUsesOfWith(outputs[i], load);
    }
  }

  SwitchInst *TheSwitch =
      SwitchInst::Create(Constant::getNullValue(Type::getInt16Ty(Context)),
                         codeReplacer, 0, codeReplacer);

  std::map<BasicBlock *, BasicBlock *> ExitBlockMap;

  unsigned switchVal = 0;
  for (BasicBlock *Block : Blocks) {
    Instruction *TI = Block->getTerminator();
    for (unsigned i = 0, e = TI->getNumSuccessors(); i != e; ++i)
      if (!Blocks.count(TI->getSuccessor(i))) {
        BasicBlock *OldTarget = TI->getSuccessor(i);
        BasicBlock *&NewTarget = ExitBlockMap[OldTarget];
        if (!NewTarget) {
          NewTarget = BasicBlock::Create(
              Context, OldTarget->getName() + ".exitStub", newFunction);
          unsigned SuccNum = switchVal++;

          Value *brVal = nullptr;
          switch (NumExitBlocks) {
          case 0:
          case 1:
            break;
          case 2:
            brVal = ConstantInt::get(Type::getInt1Ty(Context), !SuccNum);
            break;
          default:
            brVal = ConstantInt::get(Type::getInt16Ty(Context), SuccNum);
            break;
          }

          ReturnInst::Create(Context, brVal, NewTarget);

          TheSwitch->addCase(
              ConstantInt::get(Type::getInt16Ty(Context), SuccNum), OldTarget);
        }

        TI->setSuccessor(i, NewTarget);
      }
  }

  Function::arg_iterator OAI = OutputArgBegin;
  for (unsigned i = 0, e = outputs.size(); i != e; ++i) {
    auto *OutI = dyn_cast<Instruction>(outputs[i]);
    if (!OutI)
      continue;

    BasicBlock::iterator InsertPt;
    if (auto *InvokeI = dyn_cast<InvokeInst>(OutI))
      InsertPt = InvokeI->getNormalDest()->getFirstInsertionPt();
    else if (auto *Phi = dyn_cast<PHINode>(OutI))
      InsertPt = Phi->getParent()->getFirstInsertionPt();
    else
      InsertPt = std::next(OutI->getIterator());

    Instruction *InsertBefore = &*InsertPt;
    assert((InsertBefore->getFunction() == newFunction ||
            Blocks.count(InsertBefore->getParent())) &&
           "InsertPt should be in new function");
    assert(OAI != newFunction->arg_end() &&
           "Number of output arguments should match "
           "the amount of defined values");
    if (AggregateArgs) {
      Value *Idx[2];
      Idx[0] = Constant::getNullValue(Type::getInt32Ty(Context));
      Idx[1] = ConstantInt::get(Type::getInt32Ty(Context), FirstOut + i);
      GetElementPtrInst *GEP = GetElementPtrInst::Create(
          StructArgTy, &*OAI, Idx, "gep_" + outputs[i]->getName(),
          InsertBefore);
      new StoreInst(outputs[i], GEP, InsertBefore);
    } else {
      new StoreInst(outputs[i], &*OAI, InsertBefore);
      ++OAI;
    }
  }

  Type *OldFnRetTy = TheSwitch->getParent()->getParent()->getReturnType();
  switch (NumExitBlocks) {
  case 0:
    if (OldFnRetTy->isVoidTy()) {
      ReturnInst::Create(Context, nullptr, TheSwitch);
    } else if (OldFnRetTy == TheSwitch->getCondition()->getType()) {
      ReturnInst::Create(Context, TheSwitch->getCondition(), TheSwitch);
    } else {
      ReturnInst::Create(Context, Constant::getNullValue(OldFnRetTy),
                         TheSwitch);
    }

    TheSwitch->eraseFromParent();
    break;
  case 1:
    BranchInst::Create(TheSwitch->getSuccessor(1), TheSwitch);
    TheSwitch->eraseFromParent();
    break;
  case 2:
    BranchInst::Create(TheSwitch->getSuccessor(1), TheSwitch->getSuccessor(2),
                       call, TheSwitch);
    TheSwitch->eraseFromParent();
    break;
  default:
    TheSwitch->setCondition(call);
    TheSwitch->setDefaultDest(TheSwitch->getSuccessor(NumExitBlocks));
    TheSwitch->removeCase(SwitchInst::CaseIt(TheSwitch, NumExitBlocks - 1));
    break;
  }

  insertLifetimeMarkersSurroundingCall(M, ReloadOutputs, ReloadOutputs, call);

  return call;
}

void KhaosExtractor::moveCodeToFunction(Function *newFunction) {
  Function *oldFunc = (*Blocks.begin())->getParent();
  Function::BasicBlockListType &oldBlocks = oldFunc->getBasicBlockList();
  Function::BasicBlockListType &newBlocks = newFunction->getBasicBlockList();

  for (BasicBlock *Block : Blocks) {
    oldBlocks.remove(Block);

    newBlocks.push_back(Block);

    if (AC)
      for (auto &I : *Block)
        if (match(&I, m_Intrinsic<Intrinsic::assume>()))
          AC->unregisterAssumption(cast<CallInst>(&I));
  }
}

void KhaosExtractor::calculateNewCallTerminatorWeights(
    BasicBlock *CodeReplacer,
    DenseMap<BasicBlock *, BlockFrequency> &ExitWeights,
    BranchProbabilityInfo *BPI) {
  using Distribution = BlockFrequencyInfoImplBase::Distribution;
  using BlockNode = BlockFrequencyInfoImplBase::BlockNode;

  Instruction *TI = CodeReplacer->getTerminator();
  SmallVector<unsigned, 8> BranchWeights(TI->getNumSuccessors(), 0);

  Distribution BranchDist;

  for (unsigned i = 0, e = TI->getNumSuccessors(); i < e; ++i) {
    BlockNode ExitNode(i);
    uint64_t ExitFreq = ExitWeights[TI->getSuccessor(i)].getFrequency();
    if (ExitFreq != 0)
      BranchDist.addExit(ExitNode, ExitFreq);
    else
      BPI->setEdgeProbability(CodeReplacer, i, BranchProbability::getZero());
  }

  if (BranchDist.Total == 0)
    return;

  BranchDist.normalize();

  for (unsigned I = 0, E = BranchDist.Weights.size(); I < E; ++I) {
    const auto &Weight = BranchDist.Weights[I];

    BranchWeights[Weight.TargetNode.Index] = Weight.Amount;
    BranchProbability BP(Weight.Amount, BranchDist.Total);
    BPI->setEdgeProbability(CodeReplacer, Weight.TargetNode.Index, BP);
  }
  TI->setMetadata(
      LLVMContext::MD_prof,
      MDBuilder(TI->getContext()).createBranchWeights(BranchWeights));
}

Function *KhaosExtractor::extractCodeRegion(bool ConsiderRecursive) {
  ValueSet ins, outs, sinks, hoists;
  DFDep(ins, outs, sinks, true);
  if (!checkArgs(ins))
    return nullptr;
  ins.clear();
  BasicBlock *header = *Blocks.begin();
  Function *oldFunction = header->getParent();

  BasicBlock *CommonExit = nullptr;

  BlockFrequency EntryFreq;
  if (BFI) {
    assert(BPI && "Both BPI and BFI are required to preserve profile info");
    for (BasicBlock *Pred : predecessors(header)) {
      if (Blocks.count(Pred))
        continue;
      EntryFreq +=
          BFI->getBlockFreq(Pred) * BPI->getEdgeProbability(Pred, header);
    }
  }

  splitReturnBlocks();

  DenseMap<BasicBlock *, BlockFrequency> ExitWeights;
  SmallPtrSet<BasicBlock *, 1> ExitBlocks;
  for (BasicBlock *Block : Blocks) {
    for (succ_iterator SI = succ_begin(Block), SE = succ_end(Block); SI != SE;
         ++SI) {
      if (!Blocks.count(*SI)) {
        if (BFI) {
          BlockFrequency &BF = ExitWeights[*SI];
          BF += BFI->getBlockFreq(Block) * BPI->getEdgeProbability(Block, *SI);
        }
        ExitBlocks.insert(*SI);
      }
    }
  }
  NumExitBlocks = ExitBlocks.size();

  severSplitPHINodesOfEntry(header);
  severSplitPHINodesOfExits(ExitBlocks);

  DFDep(ins, outs, sinks);
  SmallVector<Type *, 8> VT = getValTypes(ins);
  for (auto it : VT) {
    switch (it->getTypeID()) {
    case Type::TypeID::VoidTyID:
    case Type::TypeID::FunctionTyID:
    case Type::TypeID::TokenTyID:
    case Type::TypeID::MetadataTyID:
      return nullptr; 
    default:;
    }
  }

  if (ins.size() > 10) {
    return nullptr;
  }
  ins.clear();
  outs.clear();

  BasicBlock *bb4CalFis =
      BasicBlock::Create(header->getContext(), "codeRepl", oldFunction, header);

  BasicBlock *newFuncRoot =
      BasicBlock::Create(header->getContext(), "newFuncRoot");
  auto *BranchI = BranchInst::Create(header);
  if (oldFunction->getSubprogram()) {
    any_of(Blocks, [&BranchI](const BasicBlock *BB) {
      return any_of(*BB, [&BranchI](const Instruction &I) {
        if (!I.getDebugLoc())
          return false;
        BranchI->setDebugLoc(I.getDebugLoc());
        return true;
      });
    });
  }
  newFuncRoot->getInstList().push_back(BranchI);

  findAllocas(sinks, hoists, CommonExit);
  assert(hoists.empty() || CommonExit);

  DFDep(ins, outs, sinks);

  AllocaInst *FirstSunkAlloca = nullptr;
  for (auto *II : sinks) {
    if (auto *AI = dyn_cast<AllocaInst>(II)) {
      AI->moveBefore(*newFuncRoot, newFuncRoot->getFirstInsertionPt());
      if (!FirstSunkAlloca)
        FirstSunkAlloca = AI;
    }
  }
  assert((sinks.empty() || FirstSunkAlloca) &&
         "Did not expect a sink candidate without any allocas");
  for (auto *II : sinks) {
    if (!isa<AllocaInst>(II)) {
      cast<Instruction>(II)->moveAfter(FirstSunkAlloca);
    }
  }

  if (!hoists.empty()) {
    auto *HoistToBlock = findOrCreateBlockForHoisting(CommonExit);
    Instruction *TI = HoistToBlock->getTerminator();
    for (auto *II : hoists)
      cast<Instruction>(II)->moveBefore(TI);
  }

  ValueSet LifetimesStart;
  eraseLifetimeMarkersOnInputs(Blocks, sinks, LifetimesStart);

  Function *newFunction =
      constructFunction(ins, outs, header, newFuncRoot, bb4CalFis, oldFunction,
                        oldFunction->getParent());

  if (BFI) {
    auto Count = BFI->getProfileCountFromFreq(EntryFreq.getFrequency());
    if (Count.hasValue())
      newFunction->setEntryCount(
          ProfileCount(Count.getValue(), Function::PCT_Real));
    BFI->setBlockFreq(bb4CalFis, EntryFreq.getFrequency());
  }

  CallInst *TheCall =
      emitCallAndSwitchStatement(newFunction, bb4CalFis, ins, outs);

  moveCodeToFunction(newFunction);

  insertLifetimeMarkersSurroundingCall(
      oldFunction->getParent(), LifetimesStart.getArrayRef(), {}, TheCall);

  if (oldFunction->hasPersonalityFn())
    newFunction->setPersonalityFn(oldFunction->getPersonalityFn());

  if (!newFunction->hasFnAttribute(Attribute::NoInline)) {
    if (newFunction->hasFnAttribute(Attribute::AlwaysInline))
      newFunction->removeFnAttr(Attribute::AlwaysInline);
    newFunction->addFnAttr(Attribute::NoInline);
  }

  if (BFI && NumExitBlocks > 1)
    calculateNewCallTerminatorWeights(bb4CalFis, ExitWeights, BPI);

  for (BasicBlock::iterator I = header->begin(); isa<PHINode>(I); ++I) {
    PHINode *PN = cast<PHINode>(I);
    for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i)
      if (!Blocks.count(PN->getIncomingBlock(i)))
        PN->setIncomingBlock(i, newFuncRoot);
  }

  for (BasicBlock *ExitBB : ExitBlocks)
    for (PHINode &PN : ExitBB->phis()) {
      Value *IncomingCodeReplacerVal = nullptr;
      for (unsigned i = 0, e = PN.getNumIncomingValues(); i != e; ++i) {
        if (!Blocks.count(PN.getIncomingBlock(i)))
          continue;

        if (!IncomingCodeReplacerVal) {
          PN.setIncomingBlock(i, bb4CalFis);
          IncomingCodeReplacerVal = PN.getIncomingValue(i);
        } else
          assert(IncomingCodeReplacerVal == PN.getIncomingValue(i) &&
                 "PHI has two incompatbile incoming values from codeRepl");
      }
    }

  for (BasicBlock &BB : *newFunction) {
    auto BlockIt = BB.begin();
    while (BlockIt != BB.end()) {
      Instruction *Inst = &*BlockIt;
      ++BlockIt;
      if (isa<DbgInfoIntrinsic>(Inst))
        Inst->eraseFromParent();
    }
    SmallVector<DbgVariableIntrinsic *, 4> DbgUsers;
    for (Instruction &I : BB)
      findDbgUsers(DbgUsers, &I);
    for (DbgVariableIntrinsic *DVI : DbgUsers)
      DVI->eraseFromParent();
  }

  bool doesNotReturn = none_of(*newFunction, [](const BasicBlock &BB) {
    const Instruction *Term = BB.getTerminator();
    return isa<ReturnInst>(Term) || isa<ResumeInst>(Term);
  });
  if (doesNotReturn)
    newFunction->setDoesNotReturn();

  LLVM_DEBUG(if (verifyFunction(*newFunction, &errs())) {
    newFunction->dump();
    report_fatal_error("verification of newFunction failed!");
  });
  LLVM_DEBUG(if (verifyFunction(*oldFunction))
                 report_fatal_error("verification of oldFunction failed!"));
  return newFunction;
}

void KhaosExtractor::fCPI(SmallVector<CatchPadInst *, 8> &vec) {
  for (BasicBlock *BB : Blocks) {
    for (Instruction &II : *BB) {
      if (CatchPadInst *CPI = dyn_cast<CatchPadInst>(&II)) {

        if (CPI->getNumArgOperands() != 1) {
          for (unsigned i = 0; i < CPI->getNumArgOperands(); i++) {
            assert(!isa<Function>(CPI->getArgOperand(i)->stripPointerCasts()) &&
                   "Filter Function found");
          }
        } else {
          Value *A = CPI->getArgOperand(0);
          if (Function *FF = dyn_cast<Function>(A->stripPointerCasts()))
            vec.push_back(CPI);
        }
      }
    }
  }
}
