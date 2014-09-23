#!/bin/bash
set -e

PKGS="SAWCore Cryptol Java LLVM SAWScript"
GITHUB_REPOS="cryptol aig abcBridge jvm-parser llvm-pretty llvm-pretty-bc-parser"
PROGRAMS="alex happy c2hs"
TESTABLE="SAWCore Java LLVM"

dotests="false"
dopull="false"
sandbox_dir=build

while getopts "tpf" opt; do
  case $opt in
    t)
      dotests="true"
      sandbox_dir=build-tests
      ;;
    f)
      force_utils="true"
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

cabal sandbox --sandbox=${sandbox_dir} init

# we have to disable library stripping on recent cabal-install versions
# to work around a bug (?) in the 32bit binutils on our install of CentOS5
if [[ ("${label}" == "saw-centos5-32") && ("${HASKELL_RUNTIME}" == "GHC783") ]]; then
  # make sure the cabal _library_ we have installed understands the option we need
  cabal install "Cabal >= 1.20"
  echo "library-stripping: False" > cabal.config
fi


# use cabal to install the build-time depencencies we need
# always build them if the '-f' option was given
for prog in ${PROGRAMS} ; do
  if [ "${force_utils}" == "true" ]; then
    cabal install $prog
  else
    (which $prog && $prog --version) || cabal install $prog
  fi
done

if [ "${dotests}" == "true" ] ; then
  for pkg in sawScript cryptol-verifier llvm-verifier jvm-verifier saw-core ; do
    cabal sandbox hc-pkg unregister $pkg || true
  done

  # prepopulate some packages to try to prevent reinstalls later
  cabal install "transformers >= 0.4"
  cabal install "QuickCheck >= 2.7.6"
  cabal install "tasty"
  cabal install "tasty-quickcheck"
  cabal install "tasty-hunit"
  cabal install "tasty-ant-xml"
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
    cabal install --force abcBridge -f-enable-pthreads
  fi
done

for pkg in ${PKGS} ; do
  cabal sandbox add-source ../${pkg}
done

if [ "${dotests}" == "true" ] ; then
  cd ..

  for pkg in ${TESTABLE}; do
    test_flags="--test-option=--xml=../${pkg}-test-results.xml --test-option=--timeout=60s"

    if [ ! "${QC_TESTS}" == "" ]; then
        test_flags="${test_flags} --test-option=--quickcheck-tests=${QC_TESTS}"
    fi

    (cd ${pkg} &&
         cabal sandbox init --sandbox="../SAWScript/${sandbox_dir}" &&
         cabal install --enable-tests --only-dependencies &&
         cabal configure --enable-tests &&
         cabal build --only &&
         (cabal test --only ${test_flags} || true))

    if [ -e ${pkg}-test-results.xml ]; then
      xsltproc jenkins-junit-munge.xsl ${pkg}-test-results.xml > jenkins-${pkg}-test-results.xml
    else
      echo "Missing test results: ${pkg}-test-results.xml"
      exit 1
    fi
  done

else

  cabal install --reinstall --force-reinstalls

fi
