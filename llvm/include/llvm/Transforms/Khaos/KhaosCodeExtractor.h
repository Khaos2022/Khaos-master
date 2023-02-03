//===- llvm/include/llvm/Transforms/Khaos/KhaosCodeExtractor.h - KhaosCode
//extraction util ---*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// A utility to support extracting code from one function into its own
// stand-alone function.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_KHAOSCODEEXTRACTOR_H
#define LLVM_TRANSFORMS_KHAOSCODEEXTRACTOR_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include <limits>

namespace llvm {

class BasicBlock;
class BlockFrequency;
class BlockFrequencyInfo;
class BranchProbabilityInfo;
class AssumptionCache;
class CallInst;
class AllocaInst;
class CatchPadInst;
class DominatorTree;
class Function;
class Instruction;
class Loop;
class Module;
class Type;
class Value;

class KhaosExtractor {
  using ValueSet = SetVector<Value *>;
  DominatorTree *const DT;
  const bool AggregateArgs;
  BlockFrequencyInfo *BFI;
  BranchProbabilityInfo *BPI;
  AssumptionCache *AC;
  bool AlVariableArgs;
  bool ConsiderRecursive;
  SetVector<BasicBlock *> Blocks;
  unsigned NumExitBlocks = std::numeric_limits<unsigned>::max();
  Type *RetTy;
  std::string Suffix;

public:
  KhaosExtractor(ArrayRef<BasicBlock *> BBs, DominatorTree *DT = nullptr,
                 bool AggregateArgs = false, BlockFrequencyInfo *BFI = nullptr,
                 BranchProbabilityInfo *BPI = nullptr,
                 AssumptionCache *AC = nullptr, bool AllowVarArgs = false,
                 bool AllowAlloca = false, std::string Suffix = "");
  KhaosExtractor(DominatorTree &DT, Loop &L, bool AggregateArgs = false,
                 BlockFrequencyInfo *BFI = nullptr,
                 BranchProbabilityInfo *BPI = nullptr,
                 AssumptionCache *AC = nullptr, std::string Suffix = "");
  Function *extractCodeRegion(bool ConsiderRecursive = false);
  bool checkArgs(const ValueSet &ins) const;
  void DFDep(ValueSet &ins, ValueSet &outs, const ValueSet &Allocs,
             bool IO = false) const;
  bool isLegalToShrinkwrapLifetimeMarkers(Instruction *AllocaAddr) const;
  void findAllocas(ValueSet &SinkCands, ValueSet &HoistCands,
                   BasicBlock *&ExitBlock) const;
  BasicBlock *findOrCreateBlockForHoisting(BasicBlock *CommonExitBlock);

private:
  struct LifetimeMarkerInfo {
    bool SinkLifeStart = false;
    bool HoistLifeEnd = false;
    Instruction *LifeStart = nullptr;
    Instruction *LifeEnd = nullptr;
  };

  LifetimeMarkerInfo getLifetimeMarkers(Instruction *Addr,
                                        BasicBlock *ExitBlock) const;

  void severSplitPHINodesOfEntry(BasicBlock *&Header);
  void severSplitPHINodesOfExits(const SmallPtrSetImpl<BasicBlock *> &Exits);
  void splitReturnBlocks();

  SmallVector<Type *, 8> getValTypes(const ValueSet &inputs) const;

  Function *constructFunction(ValueSet &inputs, ValueSet &outputs,
                              BasicBlock *header, BasicBlock *newRootNode,
                              BasicBlock *newHeader, Function *oldFunction,
                              Module *M);

  void moveCodeToFunction(Function *newFunction);

  void calculateNewCallTerminatorWeights(
      BasicBlock *CodeReplacer,
      DenseMap<BasicBlock *, BlockFrequency> &ExitWeights,
      BranchProbabilityInfo *BPI);

  CallInst *emitCallAndSwitchStatement(Function *newFunction,
                                       BasicBlock *newHeader, ValueSet &inputs,
                                       ValueSet &outputs);

  void fCPI(SmallVector<CatchPadInst *, 8> &vec);
  void fLRIAndRFP(SmallVector<CatchPadInst *, 8> &CPIvec,
                  SmallVector<CallInst *, 8> &LRIvec,
                  SmallVector<CallInst *, 8> &RFPvec);
  std::vector<CallInst *> findRecoverFp();
  AllocaInst *fEscAlloc(CallInst *CI);
};

} // end namespace llvm

#endif // LLVM_TRANSFORMS_KHAOSCODEEXTRACTOR_H
