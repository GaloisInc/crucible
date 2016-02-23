#!/bin/bash

# Download or update the dependencies.
#
# By default the latest versions are downloaded, but a
# './build-sandbox-version-pins.txt' file can be used to pin specific
# versions. See below.

set -x
set -v
set -e

PUBLIC_GITHUB_REPOS="cryptol aig abcBridge jvm-parser llvm-pretty llvm-pretty-bc-parser saw-core saw-core-aig saw-core-sbv cryptol-verifier jvm-verifier llvm-verifier"
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
# './build-sandbox-version-pins.txt'. Pin to 'master' by default.
#
# The format of the pins file entries is '<repo> <committish>'. Lines
# starting with '#' are treated as comments (because they aren't valid
# repo names). The valid repo names are the directories in './deps'.
pin () {
  repo="$1"
  committish=master
  echo Searching for pins for $repo ...
  if [ -e "$HERE"/build-sandbox-version-pins.txt ] && \
     grep "^$repo .\+\$" "$HERE"/build-sandbox-version-pins.txt &>/dev/null; then
    echo Found pins\!
    committish=$(sed -ne "s/^$repo \(.*\)\$/\1/p" < \
      "$HERE"/build-sandbox-version-pins.txt)
    echo Namely: $committish
  fi
  (
    cd "$HERE"/deps/"$repo"
    # The `fetch` is necessary before `checkout` for new branches.
    git fetch
    git checkout "$committish"
    # Pull if we are on a branch. Here `git rev-parse` returns the
    # branch name, if any, or "HEAD" if we are not on a branch (in
    # "detached head" state in Git speak).
    if [ "$(git rev-parse --abbrev-ref HEAD)" != "HEAD" ]; then
      git pull --ff-only
    fi
  )
}

# Get repos that don't exist.
for repo in ${PUBLIC_GITHUB_REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone https://github.com/GaloisInc/${repo}.git ./deps/${repo}
  fi
done
for repo in ${PRIVATE_GITHUB_REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone git@github.com:GaloisInc/${repo}.git ./deps/${repo}
  fi
done

# Update repos.
for repo in ${PUBLIC_GITHUB_REPOS} ${PRIVATE_GITHUB_REPOS}; do
  pin "$repo"
done

# Download GHC if necessary.
stack setup

# Remind what version of GHC we're using and where our binaries are
# going.
stack path
