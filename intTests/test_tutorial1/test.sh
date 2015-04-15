#!/bin/sh
set -e

mkdir -p tmp
cp ../../SAWScript/doc/tutorial/code/* tmp
cd tmp
$SAW ffs_java.saw
$SAW ffs_llvm.saw
$SAW ffs_compare.saw
$SAW ffs_gen_aig.saw
$SAW ffs_compare_aig.saw
cd ..
rm -r tmp
