#!/bin/sh
set -e

if [ "${OS}" == "Windows_NT" ]; then
  JDK="c:\\Program Files (x86)\\Java\\jre7\\lib\\rt.jar"
else
  JDK=`(java -verbose 2>&1) | grep Opened | head -1 | cut -d ' ' -f 2 | cut -d ']' -f 1`
fi

#OPTS="--sim-verbose=4 --verbose=3"
OPTS=""
${SAW:-../bin/saw} ${OPTS} -j "${JDK}" -j ecdsa.jar ecdsa.saw $*
