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

stack="stack $jobs"

if [ "${dotests}" == "true" ] ; then
  if [ -z ${TEST_TIMEOUT} ]; then
    TEST_TIMEOUT="60s"
  fi

  for pkg in ${TESTABLE}; do
    test_arguments="--xml=${HERE}/${pkg}-test-results.xml --timeout=${TEST_TIMEOUT}"

    if [ ! "${QC_TESTS}" == "" ]; then
        test_arguments="${test_arguments} --quickcheck-tests=${QC_TESTS}"
    fi

    ${stack} test --test-arguments="${test_arguments}" ${pkg}

    if [ -e ${pkg}-test-results.xml ]; then
      xsltproc jenkins-junit-munge.xsl ${pkg}-test-results.xml > jenkins-${pkg}-test-results.xml
    else
      echo "Missing test results: ${pkg}-test-results.xml"
      exit 1
    fi
  done
else
  ${stack} build
fi
