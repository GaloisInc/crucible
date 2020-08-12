DATE=`date "+%Y-%m-%d"`
PKG=crux-llvm-$DATE
rm -rf $PKG
cabal v2-build exe:crux-llvm
cabal v2-build exe:crux-llvm-svcomp
mkdir $PKG
mkdir $PKG/bin
mkdir $PKG/doc
cp `cabal v2-exec which crux-llvm` $PKG/bin
cp `cabal v2-exec which crux-llvm-svcomp` $PKG/bin
cp crux-llvm/README.md $PKG/doc
cp -r crux-llvm/c-src $PKG
tar cf $PKG.tar.gz $PKG
rm -rf $PKG
