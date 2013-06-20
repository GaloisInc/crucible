#!/bin/sh

DATE=`date "+%Y-%m-%d"`
TARGET=saw-alpha-${DATE}

NM=`uname`

mkdir -p ${TARGET}/bin
mkdir -p ${TARGET}/tutorial

if [ "${OS}" == "Windows_NT" ]; then
  EXEDIR=windows
elif [ "${NM}" == "Darwin" ]; then
  EXEDIR=macosx  
else
  EXEDIR=linux
fi

echo Staging ...

strip dist/build/saw/saw

cp build/abcBridge/abc/copyright.txt           ${TARGET}/ABC_LICENSE
cp doc/tutorial/sawScriptTutorial.pdf          ${TARGET}/tutorial
cp -r doc/tutorial/code                        ${TARGET}/tutorial
cp dist/build/saw/saw                          ${TARGET}/bin

if [ "${OS}" == "Windows_NT" ]; then
  zip -r ${TARGET}-${EXEDIR}.zip ${TARGET}
  echo "Release package is ${TARGET}-${EXEDIR}.zip"
else
  tar cvfz ${TARGET}-${EXEDIR}.tar.gz ${TARGET}
  echo "Release package is ${TARGET}-${EXEDIR}.tar.gz"
fi
