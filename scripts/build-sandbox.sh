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
# Execute this script from the `crucible-public` source repo. This will checkout all needed
# Galois dependencies in `$PWD/dependencies` and execute a build.
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
PKG_LIST="abcBridge aig blt saw-core hpb llvm-pretty llvm-pretty-bc-parser parameterized-utils"

# Set base GitHub URL for Galois repos if it's not already set
: ${GITHUB_URL:="git@github.com:GaloisInc"}
echo "Using github url: $GITHUB_URL"

# Check if 'stack' is in the path
if  type stack >/dev/null 2>&1; then
    echo "Found stack"
else
    echo >&2 "I require 'stack' but it's not installed. Aborting."
    echo >&2 "Stack available at: http://docs.haskellstack.org/en/stable/install_and_upgrade"
    exit 1
fi

if [ ! -d "dependencies" ]; then
  mkdir -p "dependencies"
fi

# Download GitHub repos
for pkg in $PKG_LIST; do
  checkout "$GITHUB_URL/$pkg.git" $pkg
done

# Download circuit-synthesis repo
checkout "git@github.com:spaceships/circuit-synthesis.git" circuit-synthesis
