#!/usr/bin/env bash
set -Eeuo pipefail

DATE=`date "+%Y-%m-%d"`
PKG=crux-mir-$DATE
EXE=`cabal v2-exec which crux-mir | tail -1`

rm -rf $PKG

mkdir $PKG
mkdir $PKG/bin
mkdir $PKG/doc

cabal v2-build exe:crux-mir
cp $EXE $PKG/bin
cp crux-mir/README.md $PKG/doc
cp -r crux-mir/rlibs $PKG

tar czf $PKG.tar.gz $PKG

rm -rf $PKG
