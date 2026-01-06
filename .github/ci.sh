#!/usr/bin/env bash
set -Eeuxo pipefail

DATE=$(date "+%Y-%m-%d")
[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

# Create a crux.buildinfo.json file for the benefit of the Crux Docker images.
# (See Note [crux.buildinfo.json] in crux/src/Crux/Version.hs.)
#
# The first argument is the git commit, and the second argument is the git
# branch name.
generate_buildinfo() {
  CI_COMMIT_SHA=$1
  CI_COMMIT_REF_NAME=$2

  jq -n \
    --arg hash "$CI_COMMIT_SHA" \
    --arg branch "$CI_COMMIT_REF_NAME" \
    --argjson dirty false \
    '{"hash": $hash, "branch": $branch, "dirty": $dirty}' \
    > crux/crux.buildinfo.json
}

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

extract_exe() {
  exe="$(cabal exec which "$1$EXT" | tail -1)"
  name="$(basename "$exe")"
  echo "Copying $name to $2"
  mkdir -p "$2"
  cp -f "$exe" "$2/$name"
  $IS_WIN || chmod +x "$2/$name"
}

configure() {
  ghc_ver="$(ghc --numeric-version)"
  cp cabal.GHC-"$ghc_ver".config cabal.project.freeze
  cabal configure "$@" --enable-tests --minimize-conflict-set --semaphore
  cat cabal.project.ci >> cabal.project.local
}

test() {
  # System-agnostic path
  export PATH="$PATH:/usr/local/opt/llvm/bin:/c/Program Files/LLVM/bin"
  ${CLANG:-:} --version || echo clang version unknown
  ${LLVM_LINK:-:} --version || echo llvm_link version unknown
  cabal test "$@"
}

install_llvm() {
  if [[ "$RUNNER_OS" = "Linux" ]]; then
    LINUX_LLVM_VER=21
    sudo .github/llvm.sh "$LINUX_LLVM_VER"
    echo "LLVM_LINK=llvm-link-$LINUX_LLVM_VER" >> "$GITHUB_ENV"
    echo "LLVM_AS=llvm-as-$LINUX_LLVM_VER" >> "$GITHUB_ENV"
    echo "CLANG=clang-$LINUX_LLVM_VER" >> "$GITHUB_ENV"
  elif [[ "$RUNNER_OS" = "macOS" ]]; then
    MACOS_LLVM_VER=21
    brew install "llvm@$MACOS_LLVM_VER"
    echo "$(brew --prefix)/opt/llvm@$MACOS_LLVM_VER/bin" >> "$GITHUB_PATH"
  elif [[ "$RUNNER_OS" = "Windows" ]]; then
    choco install llvm
  else
    echo "Unknown platform!"
    return 1
  fi
}

install_solvers() {
  (cd $BIN && \
    curl \
      --fail \
      --location \
      --proto '=https' \
      --show-error \
      --silent \
      --tlsv1.2 \
      --output bins.zip \
      "https://github.com/GaloisInc/what4-solvers/releases/download/$SOLVER_PKG_VERSION/$BUILD_TARGET_OS-$BUILD_TARGET_ARCH-bin.zip" && \
    unzip -o bins.zip && rm bins.zip)
  cp $BIN/yices_smt2$EXT $BIN/yices-smt2$EXT
  chmod +x $BIN/*
  export PATH=$BIN:$PATH
  echo "$BIN" >> "$GITHUB_PATH"
  is_exe   "$BIN" z3 && \
    is_exe "$BIN" cvc4 && \
    is_exe "$BIN" cvc5 && \
    is_exe "$BIN" boolector && \
    is_exe "$BIN" bitwuzla && \
    is_exe "$BIN" yices
}

install_system_deps() {
  install_solvers
  install_llvm
  # wait
  export PATH=$PWD/$BIN:$PATH
  echo "$PWD/$BIN" >> $GITHUB_PATH
  is_exe "$BIN" z3 && is_exe "$BIN" yices
}

sign() {
  # This is surrounded with `set +x; ...; set -x` to disable printing out
  # statements that could leak GPG-related secrets.
  set +x
  gpg --yes --quiet --batch --import <(echo "$SIGNING_KEY")
  fingerprint="$(gpg --list-keys | grep Galois -a1 | head -n1 | awk '{$1=$1};1')"
  echo "$fingerprint:6" | gpg --import-ownertrust
  gpg --yes --no-tty --batch --pinentry-mode loopback --default-key "$fingerprint" --detach-sign -o "$1".sig --passphrase-file <(echo "$SIGNING_PASSPHRASE") "$1"
  set -x
}

setup_dist() {
  rm -rf dist
  mkdir -p dist/bin dist/doc
}

zip_dist() {
  : "${VERSION?VERSION is required as an environment variable}"
  pkgname="${pkgname:-"$1-$VERSION-$OS_TAG-$ARCH_TAG"}"
  mv dist "$pkgname"
  tar -czf "$pkgname".tar.gz "$pkgname"
  rm -rf dist
}

bundle_crux_llvm_files() {
  setup_dist
  extract_exe crux-llvm dist/bin
  extract_exe crux-llvm-for-ide dist/bin
  if ! $IS_WIN; then
    extract_exe crux-llvm-svcomp dist/bin
  fi
  cp crux-llvm/README.md dist/doc
  cp -r crux-llvm/c-src dist
  VERSION=${VERSION:-$DATE}
  strip dist/bin/*
  zip_dist crux-llvm
}

bundle_crux_mir_files() {
  setup_dist
  extract_exe crux-mir dist/bin
  cp crux-mir/README.md dist/doc
  # It's less fragile to have users install mir-json themselves
  # (cd dependencies/mir-json && cargo install --locked --force --root ../../dist)
  VERSION=${VERSION:-$DATE}
  strip dist/bin/*
  zip_dist crux-mir
}

output() { echo "::set-output name=$1::$2"; }

crux_llvm_ver() { grep Version crux-llvm/crux-llvm.cabal | awk '{print $2}'; }
set_crux_llvm_version() { output crux-llvm-version "$(crux_llvm_ver)"; }

crux_mir_ver() { grep "^version:" crux-mir/crux-mir.cabal | awk '{print $2}'; }
set_crux_mir_version() { output crux-mir-version "$(crux_mir_ver)"; }

set_files() { output changed-files "$(files_since "$1" "$2")"; }
files_since() {
  changed_since="$(git log -1 --before="@{$2}")"
  files="${changed_since:+"$(git diff-tree --no-commit-id --name-only -r "$1" | xargs)"}"
  echo "$files"
}

COMMAND="$1"
shift

"$COMMAND" "$@"
