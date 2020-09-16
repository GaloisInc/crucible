#!/usr/bin/env bash
set -Eeuo pipefail

[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false

DATE=`date "+%Y-%m-%d"`
PKG=crux-llvm-$DATE
EXE=`cabal v2-exec which crux-llvm | tail -1`

rm -rf $PKG

mkdir $PKG
mkdir $PKG/bin
mkdir $PKG/doc

cabal v2-build exe:crux-llvm
cp $EXE $PKG/bin
if ! $IS_WIN ; then
  cabal v2-build exe:crux-llvm-svcomp
  EXE_SVCOMP=`cabal v2-exec which crux-llvm-svcomp | tail -1`
  cp $EXE_SVCOMP $PKG/bin
fi
cp crux-llvm/README.md $PKG/doc
cp -r crux-llvm/c-src $PKG

tar cf $PKG.tar.gz $PKG

rm -rf $PKG
