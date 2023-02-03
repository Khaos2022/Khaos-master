#include "llvm/Transforms/Khaos/Utils.h"

cl::opt<bool> EnableFus("enable-fus", cl::init(false), cl::Hidden,
		cl::desc("Enable Fus"));
cl::opt<bool> SepOnly("sep", cl::init(false), cl::Hidden,
		cl::desc("Only Fusion Fissioned Functions"));
cl::opt<bool> OriOnly("ori", cl::init(false), cl::Hidden,
		cl::desc("Only Fusion Origin Functions"));
cl::opt<bool> EnableFis("enable-fis",
				cl::desc("Enable Fission Pass"),
				cl::init(false), cl::Hidden);