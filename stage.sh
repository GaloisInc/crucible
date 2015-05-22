#!/bin/bash
set -e

while getopts "c" opt; do
    case $opt in
        c)
            # Remove './tmp', including all previous releases, before staging.
            clean="true"
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
    esac
done

DATE=`date +%F`
# Get 'Version' from the .cabal file.
VERSION=`grep Version saw-script.cabal | awk '{print $2}'`

# The last part adds '-$SYSTEM_DESC' to distinguish Jenkins Linux
# builds when 'SYSTEM_DESC' is defined. The 'SYSTEM_DESC' env var is
# defined as part of the Jenkins node configuration on the Linux
# nodes.
TARGET=tmp/saw-${VERSION}-${DATE}-`uname`-`uname -m`${SYSTEM_DESC:+-${SYSTEM_DESC}}

if [ -n "$clean" ]; then
    rm -rf ./tmp
fi
mkdir -p ${TARGET}/bin
mkdir -p ${TARGET}/doc

echo Staging ...

strip build/bin/*

cp deps/abcBridge/abc-build/copyright.txt     ${TARGET}/ABC_LICENSE
cp build/bin/bcdump                           ${TARGET}/bin
cp build/bin/extcore-info                     ${TARGET}/bin
cp build/bin/jss                              ${TARGET}/bin
cp build/bin/llvm-disasm                      ${TARGET}/bin
cp build/bin/lss                              ${TARGET}/bin
cp build/bin/saw                              ${TARGET}/bin
cp doc/extcore.txt                            ${TARGET}/doc
cp doc/tutorial/sawScriptTutorial.pdf         ${TARGET}/doc
cp -r doc/tutorial/code                       ${TARGET}/doc
#cp deps/cryptol/lib/Cryptol.cry               ${TARGET}/${CRYLIBDIR}
#cp -r ../Examples/ecdsa                       ${TARGET}/ecdsa
#rm -rf ${TARGET}/ecdsa/cryptol-2-spec
#cp -r ../Examples/zuc                         ${TARGET}/zuc

if [ "${OS}" == "Windows_NT" ]; then
  rm -f ${TARGET}.zip
  7za a -tzip ${TARGET}.zip -r ${TARGET}
  echo
  echo "Release package is ${TARGET}.zip"
else
  rm -f ${TARGET}.tar.gz
  tar cvfz ${TARGET}.tar.gz ${TARGET}
  echo
  echo "Release package is ${TARGET}.tar.gz"
fi
