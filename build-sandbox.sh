#!/bin/sh
set -e

REPODIR=${REPODIR:="src.galois.com:/srv/git"}
REPOS="abcBridge jvm-parser llvm-pretty Aiger"
PKGS="Java LLVM SAWCore Verinf"

if [ ! -e ./deps ] ; then
  mkdir deps
fi

for repo in ${REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone ${REPODIR}/${repo}.git ./deps/${repo}
  fi
done

if [ ! -e ./build ] ; then
  cabal sandbox --sandbox=./build init
fi

for pkg in ${PKGS} ; do
  cabal sandbox add-source ../${pkg}
done

for repo in ${REPOS} ; do
  cabal sandbox add-source deps/${repo}
done

cabal install
