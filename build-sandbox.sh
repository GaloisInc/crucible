#!/bin/bash
set -x
set -v
set -e

TESTABLE="saw-core jvm-verifier llvm-verifier"

dotests="false"
dopull="false"
jobs=""
while getopts "tpfj:" opt; do
    case $opt in
        t)
            dotests="true"
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

if [ ! -e ./deps -o "${dopull}" == "true" ] ; then
  ./get-dependencies.sh
fi

if [ "${OS}" == "Windows_NT" ] ; then
    HERE=$(cygpath -w $(pwd))
else
    HERE=$(pwd)
fi


if [ "${dotests}" == "true" ] ; then
  if [ -z ${TEST_TIMEOUT} ]; then
    TEST_TIMEOUT="60s"
  fi

  for pkg in ${TESTABLE}; do
    test_flags="--test-option=--xml=${HERE}/${pkg}-test-results.xml --test-option=--timeout=${TEST_TIMEOUT}"

    if [ ! "${QC_TESTS}" == "" ]; then
        test_flags="${test_flags} --test-option=--quickcheck-tests=${QC_TESTS}"
    fi

    (cd deps/${pkg} &&
         ${CABAL} sandbox init --sandbox="${HERE}/${sandbox_dir}" &&
         ${CABAL} install "${EXTRA_CONSTRAINTS}" $jobs --enable-tests --only-dependencies &&
         ${CABAL} configure "${EXTRA_CONSTRAINTS}" --enable-tests &&
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

  ${CABAL} install "${EXTRA_CONSTRAINTS}" --reinstall --force-reinstalls

fi
