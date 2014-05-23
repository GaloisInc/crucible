#!/bin/sh

DATE=`date "+%Y-%m-%d"`
TARGET=saw-alpha-${DATE}

NM=`uname`

mkdir -p ${TARGET}/bin
mkdir -p ${TARGET}/doc

if [ "${OS}" == "Windows_NT" ]; then
  EXEDIR=windows
elif [ "${NM}" == "Darwin" ]; then
  EXEDIR=macosx
else
  EXEDIR=linux
fi

echo Staging ...

strip build/bin/*

cp deps/abcBridge/abc/copyright.txt           ${TARGET}/ABC_LICENSE
cp build/bin/*                                ${TARGET}/bin
cp doc/extcore.txt                            ${TARGET}/doc
cp doc/tutorial/tutorial.*                    ${TARGET}/doc
cp -r doc/tutorial/code                       ${TARGET}/doc
rm -f build/bin/long-test
rm -f build/bin/ppsh

if [ "${OS}" == "Windows_NT" ]; then
  zip -r ${TARGET}-${EXEDIR}.zip ${TARGET}
  echo "Release package is ${TARGET}-${EXEDIR}.zip"
else
  tar cvfz ${TARGET}-${EXEDIR}.tar.gz ${TARGET}
  echo "Release package is ${TARGET}-${EXEDIR}.tar.gz"
fi
