#!/bin/sh
set -e

mkdir -p tmp
cp -r ../../Examples/ecdsa/* tmp
cd tmp
${SAW} -j ecdsa.jar ecdsa.saw
cd ..
rm -r tmp
