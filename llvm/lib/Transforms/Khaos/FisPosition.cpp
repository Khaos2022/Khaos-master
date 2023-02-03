//===- FisPosition.cpp ------------------------------------- ---------------===//
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

#include "llvm/Transforms/Khaos/Utils.h"

static cl::opt<int> fisPosGS("fis-pos-gs", cl::init(5), cl::Hidden,
                               cl::desc("group size"));


namespace {
    struct FisPosPass : public ModulePass {
        static char ID;
        FisPosPass() : ModulePass(ID) {}
        bool runOnModule(Module &M) override;
        vector<Function*> colFuncs(Module &M);
    };
}

bool FisPosPass::runOnModule(Module &M) {
    vector<Function*> FV = colFuncs(M);
    size_t FN = FV.size();
    bool MC = false;
    for (size_t i = 0; i < FN; i++) {
        size_t j = (rand() % (FN - i)) % fisPosGS + i;
        if (i == j) return MC;
        Function* F1 = FV[i];
        Function* F2 = FV[j];
        Function* F3 = FV[j - 1];
        FV[i] = F2;
        FV[j] = F1;
        M.getFunctionList().splice(F1->getIterator(), M.getFunctionList(), F2->getIterator());
        M.getFunctionList().splice(++F3->getIterator(), M.getFunctionList(), F1->getIterator());
        MC = true;
    }
	return MC;
}

vector<Function*> FisPosPass::colFuncs(Module &M){
    vector<Function*> FV;
    for (auto i = M.begin(); i != M.end(); i++) {
        Function *F = &(*i);
        if (F->isIntrinsic() || F->isDeclaration()) continue;
        FV.push_back(F);
        if (!F->isExternalLinkage && !F->isAbsoluteSymbolRef() && EnableFus)
            F->setName("");
    }
    return FV;
}

char FisPosPass::ID = 0;
static RegisterPass<FisPosPass> X("fisPosPass", "FisPosition Pass");

ModulePass *llvm::createFisPositionPass() {
    return new FisPosPass();
}
