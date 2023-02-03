add_llvm_library( LLVMKhaosMid
  Utils.cpp
  Fus.cpp
  FisPosition.cpp
  KhaosCodeExtractor.cpp
  Fis.cpp
)

add_dependencies(LLVMKhaosMid intrinsics_gen)
