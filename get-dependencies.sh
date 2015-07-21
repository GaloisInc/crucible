#!/bin/bash

# Download or update the dependencies.
#
# By default the latest versions are downloaded, but a
# './build-sandbox-version-pins.txt' file can be used to pin specific
# versions. See below.

set -x
set -v
set -e

PUBLIC_GITHUB_REPOS="cryptol aig abcBridge jvm-parser llvm-pretty llvm-pretty-bc-parser saw-core cryptol-verifier jvm-verifier llvm-verifier"
PRIVATE_GITHUB_REPOS=""

if [ ! -e ./deps ] ; then
  mkdir deps
fi

if [ "${OS}" == "Windows_NT" ] ; then
    HERE=$(cygpath -w $(pwd))
else
    HERE=$(pwd)
fi

# Pin a repo *if* a corresponding pin is defined in
# './build-sandbox-version-pins.txt'. Assumes the CWD is in the
# argument repo.
#
# The format of the pins file entries is '<repo> <committish>'. Lines
# starting with '#' are treated as comments (because they aren't valid
# repo names).
pin () {
  repo="$1"
  echo Searching for pins for $repo ...
  if [ -e "$HERE"/build-sandbox-version-pins.txt ] && \
     grep "^$repo .\+\$" "$HERE"/build-sandbox-version-pins.txt &>/dev/null; then
    echo Found pins\!
    committish=$(sed -ne "s/^$repo \(.*\)\$/\1/p" < \
      "$HERE"/build-sandbox-version-pins.txt)
    echo Namely: $committish
    git reset --hard "$committish"
  fi
}

for repo in ${PUBLIC_GITHUB_REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone https://github.com/GaloisInc/${repo}.git ./deps/${repo}
  else
    (cd ./deps/${repo} && git checkout master && git pull && pin "$repo")
  fi
done

for repo in ${PRIVATE_GITHUB_REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone git@github.com:GaloisInc/${repo}.git ./deps/${repo}
  else
    (cd ./deps/${repo} && git checkout master && git pull && pin "$repo")
  fi
done

# Download GHC if necessary.
stack setup
