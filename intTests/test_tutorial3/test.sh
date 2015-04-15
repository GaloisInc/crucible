#!/bin/sh
set -e

mkdir -p tmp
cp ../../SAWScript/doc/tutorial/code/* tmp
cd tmp
$SAW nqueens.saw
cd ..
rm -r tmp
