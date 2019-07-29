rm *~
cd ..
cabal new-build
cd src
clang++ -c -emit-llvm test.cpp
ghci CruxLLVMMain.hs
