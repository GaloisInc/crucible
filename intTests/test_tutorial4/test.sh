#!/bin/sh
set -e

mkdir -p tmp
cp -r ../../deps/llvm-verifier/sym-api tmp
cp -r ../../deps/llvm-verifier/doc/lss-tutorial/code/* tmp
cd tmp
# assume the .bc is already built
# the build slaves don't generally have LLVM installed
# make SYMAPI=sym-api aes.bc
$LSS aes.bc

$SAW aes.saw
cd ..
rm -r tmp
