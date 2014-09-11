#!/bin/bash
set -e

PKGS="Verinf SAWCore Cryptol Java LLVM"
GITHUB_REPOS="cryptol aig abcBridge jvm-parser llvm-pretty llvm-pretty-bc-parser"
PROGRAMS="alex happy c2hs"

cabal_flags="--reinstall --force-reinstalls"
dotests="false"
dopull="false"
sandbox_dir=build

while getopts "tp" opt; do
  case $opt in
    t)
      dotests="true"
      sandbox_dir=build-tests
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

PWD=`pwd`
PATH=${PWD}/${sandbox_dir}/bin:$PATH
sandbox_dir=${PWD}/${sandbox_dir}

cabal sandbox --sandbox=${sandbox_dir} init

for prog in ${PROGRAMS} ; do
  if [ -z `which $prog` ] ; then cabal install $prog ; fi
done

if [ "${dotests}" == "true" ] ; then
  for pkg in sawScript cryptol-verifier llvm-verifier jvm-verifier saw-core Verinf ; do
    cabal sandbox hc-pkg unregister $pkg || true
  done
fi

for repo in ${GITHUB_REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone https://github.com/GaloisInc/${repo}.git ./deps/${repo}
  fi
  if [ "${dopull}" == "true" ] ; then
    (cd ./deps/${repo} && git checkout master && git pull)
  fi
done

(cd deps/cryptol && sh configure)

for repo in ${GITHUB_REPOS} ; do
  cabal sandbox add-source deps/${repo}

  # Be sure abcBridge builds with pthreads diabled on Windows
  if [ "${OS}" == "Windows_NT" -a "${repo}" == "abcBridge" ]; then
    cabal install --force abcBridge ${cabal_flags} -f-enable-pthreads
  fi
done

for pkg in ${PKGS} ; do
  cabal sandbox add-source ../${pkg}
done

if [ "${dotests}" == "true" ] ; then
  for pkg in ${PKGS}; do
      (cd ../${pkg} &&
         cabal sandbox init --sandbox=${sandbox_dir} &&
	 cabal install --enable-tests --only-dependencies &&
         cabal configure --enable-tests &&
	 (cabal test -v --only --test-option=--xml=../${pkg}-test-results.xml --test-option=--timeout=60s || true))
  done

else

  cabal install ${cabal_flags}

fi
