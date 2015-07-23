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

# Warn if 'SYSTEM_DESC' is not defined. The 'SYSTEM_DESC' env var is
# defined as part of the Jenkins node configuration on the Linux
# nodes.
RELEASE=saw-${VERSION}-${DATE}-${SYSTEM_DESC:-SYSTEM_DESC-IS-NOT-DEFINED}
TARGET=tmp/release/$RELEASE

if [ -n "$clean" ]; then
    rm -rf ./tmp/release
fi
mkdir -p ${TARGET}/bin
mkdir -p ${TARGET}/doc

echo Staging ...

# Workaround bug which prevents using `stack path --local-install-root`:
# https://github.com/commercialhaskell/stack/issues/604.
BIN=$(stack path | sed -ne 's/local-install-root: //p')/bin

strip "$BIN"/*

cp deps/abcBridge/abc-build/copyright.txt     ${TARGET}/ABC_LICENSE
cp LICENSE                                    ${TARGET}/LICENSE
cp "$BIN"/bcdump                              ${TARGET}/bin
cp "$BIN"/extcore-info                        ${TARGET}/bin
cp "$BIN"/jss                                 ${TARGET}/bin
cp "$BIN"/llvm-disasm                         ${TARGET}/bin
cp "$BIN"/lss                                 ${TARGET}/bin
cp "$BIN"/saw                                 ${TARGET}/bin
cp doc/extcore.txt                            ${TARGET}/doc
cp doc/tutorial/sawScriptTutorial.pdf         ${TARGET}/doc
cp -r doc/tutorial/code                       ${TARGET}/doc

cd tmp/release
if [ "${OS}" == "Windows_NT" ]; then
  rm -f ${RELEASE}.zip
  7za a -tzip ${RELEASE}.zip -r ${RELEASE}
  echo
  echo "Release package is `pwd`/${RELEASE}.zip"
else
  rm -f ${RELEASE}.tar.gz
  tar cvfz ${RELEASE}.tar.gz ${RELEASE}
  echo
  echo "Release package is `pwd`/${RELEASE}.tar.gz"
fi
