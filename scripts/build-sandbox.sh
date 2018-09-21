#!/bin/bash
#
# This script checks out the repos needed to build crucible libraries and the crucible-server.
#
# This script only requires git to run, but crucible has the following prerequites:
#
#   * stack
#      - https://github.com/commercialhaskell/stack/wiki/Downloads
#
#   * Libraries & Utils: pkg-config, libzmq, NTL, GLPK, Boost
#      - to install NTL, GLPK, and Boost easily, see:
#        https://github.com/GaloisInc/blt/blob/master/bootstrap.sh
#      - to install pkg-config and libzmq on Debian/Ubuntu, do:
#        $ sudo apt-get install pkg-config libzmq3 libzmq3-dev
#
#   * GHC >= 7.10 (Optional)
#      - https://www.haskell.org/ghc/download
#
# Installation:
#
# Execute this script from the top level of the `crucible-public` source repo.
# This will checkout all needed Galois dependencies in `$PWD/dependencies`.
#
# Options:
#
# Set $NO_GIT_PULL if you do not want to 'git pull' in pre-existing dependency repos.
#

set -e

checkout () {
  local url=$1 # File to unpack
  local pkg=$2
  if [ ! -d "dependencies/$pkg" ]; then
      pushd dependencies > /dev/null
      git clone "$url"
      if [ $? -ne 0 ]; then
          echo "\n\nFailed to clone private GitHub repos. Please check your \
                ssh keys to make sure you are authorized for the Galois GitHub \
                account"
          exit 1
      fi
      popd > /dev/null
  elif [ -z "${NO_GIT_PULL}" ]; then
      echo "Pulling from $pkg"
      pushd "dependencies/$pkg" > /dev/null
      git pull
      popd > /dev/null
  fi
}

# GitHub repos (some private, some public) required by the build
PKG_LIST="GaloisInc/abcBridge GaloisInc/aig GaloisInc/blt \
          GaloisInc/saw-core GaloisInc/saw-core-aig GaloisInc/saw-core-sbv \
          GaloisInc/saw-core-what4 \
	  GaloisInc/hpb elliottt/llvm-pretty \
	  GaloisInc/jvm-parser \
	  GaloisInc/cryptol GaloisInc/cryptol-verifier \
	  elliottt/llvm-pretty \
          GaloisInc/llvm-pretty-bc-parser GaloisInc/parameterized-utils"

# Set base GitHub URL for Galois repos if it's not already set
: ${GITHUB_URL:="git@github.com:"}
echo "Using github url: $GITHUB_URL"

if [ ! -d "dependencies" ]; then
  mkdir -p "dependencies"
fi

# Download GitHub repos
for pkg in $PKG_LIST; do
  checkout "$GITHUB_URL$pkg.git" ${pkg#*/}
done
