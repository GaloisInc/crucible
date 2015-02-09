#!/bin/bash
set -x
set -e

PKGS="SAWCore Cryptol Java LLVM SAWScript"
GITHUB_REPOS="cryptol aig abcBridge jvm-parser llvm-pretty llvm-pretty-bc-parser"
PROGRAMS="alex happy c2hs"
TESTABLE="SAWCore Java LLVM"

dotests="false"
dopull="false"
sandbox_dir=build

while getopts "tpfj:" opt; do
    case $opt in
        t)
            dotests="true"
            ;;
        f)
            force_utils="true"
            ;;
        p)
            dopull="true"
            ;;
        j)
            jobs="-j$OPTARG"
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
    esac
done

if [ ! -e ./deps ] ; then
  mkdir deps
fi

if [ "${OS}" == "Windows_NT" ] ; then
    HERE=$(cygpath -w $(pwd))
else
    HERE=$(pwd)
fi

PATH=${HERE}/${sandbox_dir}/bin:$PATH
CABAL="cabal"

if [ ! -e ${sandbox_dir} ] ; then
    for pkg in ${PKGS} ; do
        (cd ${HERE}/../$pkg && ${CABAL} sandbox --sandbox="${HERE}/${sandbox_dir}" init)
    done
fi

if [ "${dotests}" == "true" ] ; then
  for pkg in sawScript llvm-verifier jvm-verifier cryptol-verifier saw-core ; do
    ${CABAL} sandbox hc-pkg unregister $pkg || true
  done
fi

# use cabal to install the build-time depencencies we need
# always build them if the '-f' option was given
for prog in ${PROGRAMS} ; do
  if [ "${force_utils}" == "true" ]; then
    ${CABAL} install $jobs $prog
  else
    (which $prog && $prog --version) || ${CABAL} install $jobs $prog
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

for repo in ${GITHUB_REPOS} ; do
  ${CABAL} sandbox add-source deps/${repo}

  # Be sure abcBridge builds with pthreads diabled on Windows
  if [ "${OS}" == "Windows_NT" -a "${repo}" == "abcBridge" ]; then
    ${CABAL} install $jobs --force abcBridge -f-enable-pthreads
  fi
done

for pkg in ${PKGS} ; do
  ${CABAL} sandbox add-source ../${pkg}
done

if [ "${dotests}" == "true" ] ; then
  cd ..

  if [ -z ${TEST_TIMEOUT} ]; then
    TEST_TIMEOUT="60s"
  fi

  for pkg in ${TESTABLE}; do
    test_flags="--test-option=--xml=../${pkg}-test-results.xml --test-option=--timeout=${TEST_TIMEOUT}"

    if [ ! "${QC_TESTS}" == "" ]; then
        test_flags="${test_flags} --test-option=--quickcheck-tests=${QC_TESTS}"
    fi

    (cd ${pkg} &&
         ${CABAL} sandbox init --sandbox="${HERE}/${sandbox_dir}" &&
         ${CABAL} install $jobs --enable-tests --only-dependencies &&
         ${CABAL} configure --enable-tests &&
         ${CABAL} build &&
         (${CABAL} test ${test_flags} || true))

    if [ -e ${pkg}-test-results.xml ]; then
      xsltproc jenkins-junit-munge.xsl ${pkg}-test-results.xml > jenkins-${pkg}-test-results.xml
    else
      echo "Missing test results: ${pkg}-test-results.xml"
      exit 1
    fi
  done

else

  ${CABAL} install --reinstall --force-reinstalls

fi
