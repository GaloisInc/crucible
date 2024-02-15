#!/bin/env bash
set -Eeuxo pipefail

DATE=$(date "+%Y-%m-%d")
EXT=""
IS_WIN=false
OS_TAG=Linux
ARCH_TAG=X64
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

extract_exe() {
  exe="$(cabal v2-exec which "$1$EXT" | tail -1)"
  name="$(basename "$exe")"
  echo "Copying $name to $2"
  mkdir -p "$2"
  cp -f "$exe" "$2/$name"
  $IS_WIN || chmod +x "$2/$name"
}

setup_dist() {
  rm -rf dist
  mkdir -p dist/bin dist/doc
}

zip_dist() {
  : "${VERSION?VERSION is required as an environment variable}"
  pkgname="${pkgname:-"$1-$VERSION-$OS_TAG-$ARCH_TAG"}"
  mv dist "$pkgname"
  zip -r "$pkgname".zip "$pkgname"
  rm -rf dist
}

bundle_crux_llvm_svcomp_files() {
  setup_dist
  extract_exe crux-llvm dist/bin
  if ! $IS_WIN; then
    extract_exe crux-llvm-svcomp dist/bin
  fi
  cp -r ../c-src dist

  # SV-COMP–specific requirements begin
  ## SMT solvers
  cp "$(which cvc4)"       dist/bin/
  cp "$(which yices)"      dist/bin/
  cp "$(which yices-smt2)" dist/bin/
  cp "$(which z3)"         dist/bin/
  ## LLVM binaries
  cp "$(which clang)"      dist/bin/
  cp "$(which llvm-link)"  dist/bin/
  ## A wrapper script for crux-llvm-svcomp that puts the aforementioned
  ## binaries on the PATH before invocation
  cp crux-llvm-svcomp-driver.sh dist/
  ## Competition-specific configuration files
  cp config-files/*.config dist/
  ## The LICENSE and README (a particular SV-COMP requirement listed in
  ## https://sv-comp.sosy-lab.org/2021/rules.php#verifier)
  cp ../LICENSE dist/
  cp ../README.md dist/README

  VERSION=${VERSION:-$DATE}
  zip_dist crux-llvm-svcomp
}

# Make sure executables are up to date
cabal build exe:crux-llvm exe:crux-llvm-svcomp

# Extend PATH to include LLVM binaries
PATH=$SCRIPT_DIR/clang/bin:$PATH

# Make sure we're in the right directory
cd "$SCRIPT_DIR" || exit

# Create the bindist
bundle_crux_llvm_svcomp_files
