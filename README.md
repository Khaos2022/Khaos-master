# Khaos
## Source Code
Khaos is an inter-procedural obfuscation prototype based on LLVM 9.0.1. It mainly contains two passes, fission pass and fusion pass. These codes are mainly in Khaos/llvm/lib/Transforms/Khaos.

Fis.cpp	Fission pass

Fus.cpp	Fusion pass


Khaos can be rebuilt from source code same as LLVM. We use following command to build Khaos:
```
mkdir build && cd build
cmake -G Ninja -DLLVM_ENABLE_PROJECTS="clang;libcxx;libcxxabi;compiler-rt;lld" -DLLVM_TARGETS_TO_BUILD=X86 /path/to/Khaos/llvm
ninja
```
## Usage
The obfuscation mode is set by command args. There are 5 modes in Khaos.

Fission
```
/path/to/Khaos/release/clang -flto -fuse-ld=lld -O2 -mllvm -enable-fis xxx.c yyy.c zzz.c
```

Fusion
```
/path/to/Khaos/release/clang -flto -fuse-ld=lld -O2 -mllvm -enable-fus -fno-discard-value-names -w /path/to/Khaos/fusion_helper.o xxx.c yyy.c zzz.c
```

FuFi.sep
```
/path/to/Khaos/release/clang -flto -fuse-ld=lld -O2 -mllvm -enable-fis -mllvm -enable-fus  -mllvm -sep -fno-discard-value-names -w /path/to/Khaos/fusion_helper.o xxx.c yyy.c zzz.c
```

FuFi.ori
```
/path/to/Khaos/release/clang -flto -fuse-ld=lld -O2 -mllvm -enable-fis    -mllvm -enable-fus  -mllvm -ori -fno-discard-value-names -w /path/to/Khaos/fusion_helper.o xxx.c yyy.c zzz.c
```

FuFi.all
```
/path/to/Khaos/release/clang -flto -fuse-ld=lld -O2 -mllvm -enable-fis    -mllvm -enable-fus  -fno-discard-value-names -w /path/to/Khaos/fusion_helper.o xxx.c yyy.c zzz.c
```

## Paper
If you find Khaos useful, please cite our paper in CGO'23:
```
Peihua Zhang, Chenggang Wu, Mingfan Peng, Kai Zeng, Ding Yu, Yuanming Lai, Yan Kang, Wei Wang, and Zhe Wang. 2023. Khaos: The Impact of Inter-procedural Code Obfuscation on Binary Diffing Techniques. In Proceedings of the 21st ACM/IEEE International Symposium on Code Generation and Optimization (CGO ’23), February 25 – March 1, 2023, Montréal, QC, Canada. ACM, New York, NY, USA, 13 pages. https://doi.org/10.1145/3579990.3580007
```
