#!/bin/bash
set -e

REPODIR=${REPODIR:="src.galois.com:/srv/git"}
REPOS="aig abcBridge jvm-parser llvm-pretty Aiger"
PKGS="Verinf SAWCore Java LLVM Cryptol"
GITHUB_REPOS="cryptol"

cabal_flags="--reinstall --force-reinstalls"
test_flags="--enable-tests --run-tests --disable-library-coverage"
dotests="false"
dopull="false"
while getopts "tp" opt; do
  case $opt in
    t)
      cabal_flags="${cabal_flags} ${test_flags}"
      dotests="true"
      ;;
    p) dopull="true" ;;
    \?)
      echo "Invalid option: -$OPTARG" >&2
      exit 1
      ;;
  esac
done

if [ ! -e ./deps ] ; then
  mkdir deps
fi

for repo in ${REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone ${REPODIR}/${repo}.git ./deps/${repo}
  fi
  if [ "${dopull}" == "true" ] ; then
    (cd ./deps/${repo} && git checkout master && git pull)
  fi
done

for repo in ${GITHUB_REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone https://github.com/GaloisInc/${repo}.git ./deps/${repo}
  fi
  if [ "${dopull}" == "true" ] ; then
    (cd ./deps/${repo} && git checkout master && git pull)
  fi
done

if [ ! -e ./build ] ; then
  cabal sandbox --sandbox=./build init
fi

for repo in ${REPOS} ${GITHUB_REPOS} ; do
  cabal sandbox add-source deps/${repo}
  if [ "${dotests}" == "true" ] ; then
    cabal install ${repo} ${cabal_flags}
  fi
done

for pkg in ${PKGS} ; do
  cabal sandbox add-source ../${pkg}
  if [ "${dotests}" == "true" ] ; then
    cabal install ../${pkg} ${cabal_flags}
  fi
done

cabal install ${cabal_flags}
