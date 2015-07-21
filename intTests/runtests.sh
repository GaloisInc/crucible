#!/bin/bash

################################################################
# Setup environment.

if [ -z "$TESTBASE" ]; then
  export TESTBASE=`pwd`
fi
JSS_BASE=$TESTBASE/../deps/jvm-verifier

# define the BIN variable, if not already defined
if [ -z "$BIN" ]; then
  # Workaround bug which prevents using `stack path --local-install-root`:
  # https://github.com/commercialhaskell/stack/issues/604.
  BIN="$(cd "$TESTBASE"/.. &&
    stack path | sed -ne 's/local-install-root: //p')"/bin
  if [ "$OS" = "Windows_NT" ]; then
    # Stack returns Windows paths on Windows, but we're using Cygwin so
    # we want Unix paths.
    BIN=$(cygpath -u "$BIN")
  fi
fi

if [ "${OS}" == "Windows_NT" ]; then
  export CPSEP=";"
  export DIRSEP="\\"
else
  export CPSEP=":"
  export DIRSEP="/"
fi
export PATH=$BIN:$PATH

# Build the class path. On Windows, Java requires Windows-style paths
# here, even in Cygwin.
#
# Locate rt.jar. This is already a Windows path on windows, so no need
# to 'cygpath' it.
JDK=$("$JSS_BASE"/find-java-rt-jar.sh)
CP="$JDK"
# Add our bundled .jars to the class path.
for i in "$TESTBASE"/jars/*.jar "$JSS_BASE"/jars/*.jar; do
  if [ "$OS" == "Windows_NT" ]; then
    i=$(cygpath -w "$i")
  fi
  CP=$CP$CPSEP$i
done
export CP

# We need the 'eval's here to interpret the single quotes protecting
# the spaces and semi-colons in the Windows class path.
export SAW="eval saw -j '$CP'"
export JSS="eval jss -j '$CP' -c ."
export LSS="lss"

# Figure out what tests to run
if [[ -z "$@" ]]; then
  if [ -z "$DISABLED_TESTS" ]; then
    # File listing tests disabled by default.
    DISABLED_TESTS=disabled_tests.txt
  fi
  # Collect tests not listed in the disabled tests.
  TESTS=""
  for t in test*; do
    if ! grep -q "^$t\$" $DISABLED_TESTS; then
        TESTS="$TESTS $t"
    fi
  done
else
  # Default disabled tests are ignored when specific tests are
  # specified on the command line.
  TESTS=$@
fi

if [ -z "${TEST_TIMEOUT}" ]; then
  TEST_TIMEOUT=300
fi

if [ -z "${XML_FILE}" ]; then
  XML_FILE="results.xml"
fi
XML_TEMP="${XML_FILE}.tmp"

################################################################
# Run tests.

mkdir -p logs
rm -f logs/*

NUM_TESTS=0
FAILED_TESTS=0
export TIMEFORMAT="%R"
TOTAL_TIME=0

for i in $TESTS; do
  NUM_TESTS=$(( $NUM_TESTS + 1 ))

  # Some nasty bash hacking here to catpure the amount of time taken by the test
  # See http://mywiki.wooledge.org/BashFAQ/032
  if [ "${OS}" == "Windows_NT" ]; then
    # ulimit is useless on cygwin :-(  Use the 'timeout' utility instead
    TEST_TIME=$(cd $i; (time /usr/bin/timeout -k 15 ${TEST_TIMEOUT} sh -vx test.sh > ../logs/$i.log 2>&1) 2>&1 )
    RES=$?
  else
    TEST_TIME=$(ulimit -t ${TEST_TIMEOUT}; cd $i; (time sh -vx test.sh > ../logs/$i.log 2>&1) 2>&1 )
    RES=$?
  fi

  if [ $(echo "$TEST_TIME >= $TEST_TIMEOUT" | bc) == 1 ]; then
    TIMED_OUT=" TIMEOUT"
  else
    TIMED_OUT=""
  fi

  TOTAL_TIME=$( echo "${TOTAL_TIME} + ${TEST_TIME}" | bc )

  if [ $RES == 0 ]; then
    echo "$i: OK ($TEST_TIME)"
    echo "  <testcase name=\"${i}\" time=\"${TEST_TIME}\" />" >> ${XML_TEMP}
  else
    echo "$i: FAIL ($TEST_TIME$TIMED_OUT)"
    if [ ! -z "$LOUD" ]; then cat logs/$i.log; fi
    FAILED_TESTS=$(( $FAILED_TESTS + 1 ))
    echo "  <testcase name=\"${i}\" time=\"${TEST_TIME}\"><failure><![CDATA[" >> ${XML_TEMP}
    sed -e 's/]]>/] ]>/' logs/$i.log >> ${XML_TEMP}
    echo "]]></failure></testcase>" >> ${XML_TEMP}
  fi
done

echo "<?xml version='1.0'?>" > $XML_FILE
echo "<testsuites errors=\"${FAILED_TESTS}\" tests=\"${NUM_TESTS}\" time=\"${TOTAL_TIME}\">" >> $XML_FILE
echo " <testsuite name=\"SAWScript Integration Tests\">" >> $XML_FILE
cat $XML_TEMP >> $XML_FILE
echo " </testsuite>" >> $XML_FILE
echo "</testsuites>" >> $XML_FILE
rm $XML_TEMP

echo "tests completed"
