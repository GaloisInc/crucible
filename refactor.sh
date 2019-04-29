#!/usr/bin/env bash

for file in $(find crucible{-llvm,-saw,-server,-syntax}/src crux{,-llvm}/src what4{,-abc,-blt}/src -iname "*.hs" -type f ); do
  hlint "$file" --refactor --refactor-options="-i"
done
