#!/bin/bash
set -e

DATE=`date +%F`
# Get 'Version' from the .cabal file.
VERSION=`grep Version saw-script.cabal | awk '{print $2}'`

TARGET=tmp/saw-${VERSION}-${DATE}-`uname`-`uname -m`

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
  7za.exe a -tzip ${TARGET}.zip -r ${TARGET}
  echo
  echo "Release package is ${TARGET}.zip"
else
  rm -f ${TARGET}.tar.gz
  tar cvfz ${TARGET}.tar.gz ${TARGET}
  echo
  echo "Release package is ${TARGET}.tar.gz"
fi
