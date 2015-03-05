#!/bin/sh
set -e

DATE=`date "+%Y-%m-%d"`
TARGET=saw-alpha-${DATE}

NM=`uname`

if [ "${OS}" == "Windows_NT" ]; then
  EXEDIR=windows
  CRYLIBDIR=cryptol
elif [ "${NM}" == "Darwin" ]; then
  EXEDIR=macosx
  CRYLIBDIR=share/cryptol
else
  EXEDIR=linux
  CRYLIBDIR=share/cryptol
fi

mkdir -p ${TARGET}/bin
mkdir -p ${TARGET}/doc
mkdir -p ${TARGET}/${CRYLIBDIR}

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
cp deps/cryptol/lib/Cryptol.cry               ${TARGET}/${CRYLIBDIR}
cp -r ../Examples/ecdsa                       ${TARGET}/ecdsa
cp -r ../Examples/zuc                         ${TARGET}/zuc
rm -rf ${TARGET}/ecdsa/cryptol-2-spec

if [ "${label}" == "Chair" ]; then
  7za.exe a -tzip ${TARGET}-${EXEDIR}.zip -r ${TARGET}
  echo "Release package is ${TARGET}-${EXEDIR}.zip"
else
  tar cvfz ${TARGET}-${EXEDIR}.tar.gz ${TARGET}
  echo "Release package is ${TARGET}-${EXEDIR}.tar.gz"
fi
