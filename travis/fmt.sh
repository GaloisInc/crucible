#!/usr/bin/env bash

# Generate .travis.yml from the Dhall

fmt() {
  cmd="cat $1 | dhall format > $1.fmt && mv $1.fmt $1"
  if command -v nix-shell; then
    # https://github.com/commercialhaskell/stack/issues/793
    nix-shell -p glibcLocales -p dhall --pure --run "export LANG=en_US.utf8 && $cmd"
  else
    $cmd
  fi
}

for f in *.dhall; do
  fmt "$f"
done
