#!/usr/bin/env bash
set -Eeuo pipefail

DATE=`date "+%Y-%m-%d"`
PKG=crux-llvm-$DATE
EXE=`cabal v2-exec which crux-llvm`
EXE_SVCOMP=`cabal v2-exec which crux-llvm-svcomp || true`

rm -rf $PKG

mkdir $PKG
mkdir $PKG/bin
mkdir $PKG/doc

cp $EXE $PKG/bin
if [ -e "$EXE_SVCOMP" ] ; then
  cp $EXE_SVCOMP $PKG/bin
fi
cp crux-llvm/README.md $PKG/doc
cp -r crux-llvm/c-src $PKG

tar cf $PKG.tar.gz $PKG

rm -rf $PKG
