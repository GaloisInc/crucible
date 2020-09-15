#!/usr/bin/env bash
set -Eeuo pipefail

[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false

DATE=`date "+%Y-%m-%d"`
PKG=crux-llvm-$DATE
EXE=`cabal v2-exec which crux-llvm`
EXE_SVCOMP=`cabal v2-exec which crux-llvm-svcomp || true`

rm -rf $PKG

mkdir $PKG
mkdir $PKG/bin
mkdir $PKG/doc

cp $EXE $PKG/bin
$IS_WIN || cp $EXE_SVCOMP $PKG/bin
cp crux-llvm/README.md $PKG/doc
cp -r crux-llvm/c-src $PKG

tar cf $PKG.tar.gz $PKG

rm -rf $PKG
