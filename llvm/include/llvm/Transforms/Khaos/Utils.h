#ifndef LLVM_KHAOS_UTILS_H
#define LLVM_KHAOS_UTILS_H

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Pass.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/PassRegistry.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/CodeGen/ISDOpcodes.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/InitializePasses.h"
#include "llvm/PassSupport.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/Cloning.h"


#include <vector>
#include <map>
#include <set>
#include <string>
#include <queue>
#include <stack>
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>
#include <stdio.h>
#include <sstream>
#include <list>

using namespace llvm;
using namespace std;

namespace llvm {
    class ModulePass;
    extern ModulePass *createFusPass();
    extern ModulePass *createFisPass(); 
    extern ModulePass *createFisPositionPass();
}

extern cl::opt<bool> EnableFus;
extern cl::opt<bool> EnableFis;
extern cl::opt<bool> SepOnly;
extern cl::opt<bool> OriOnly;
#endif