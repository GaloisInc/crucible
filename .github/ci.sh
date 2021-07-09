#!/usr/bin/env bash
set -Eeuxo pipefail

DATE=$(date "+%Y-%m-%d")
[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

extract_exe() {
  exe="$(cabal v2-exec which "$1$EXT" | tail -1)"
  name="$(basename "$exe")"
  echo "Copying $name to $2"
  mkdir -p "$2"
  cp -f "$exe" "$2/$name"
  $IS_WIN || chmod +x "$2/$name"
}

retry() {
  echo "Attempting with retry:" "$@"
  local n=1
  while true; do
    if "$@"; then
      break
    else
      if [[ $n -lt 3 ]]; then
        sleep $n # don't retry immediately
        ((n++))
        echo "Command failed. Attempt $n/3:"
      else
        echo "The command has failed after $n attempts."
        exit 1
      fi
    fi
  done
}

install_z3() {
  is_exe "$BIN" "z3" && return

  case "$RUNNER_OS" in
    Linux) file="ubuntu-16.04.zip" ;;
    macOS) file="osx-10.14.6.zip" ;;
    Windows) file="win.zip" ;;
  esac
  curl -o z3.zip -L "https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION/z3-$Z3_VERSION-x64-$file"

  if $IS_WIN; then 7z x -bd z3.zip; else unzip z3.zip; fi
  cp z3-*/bin/z3$EXT $BIN/z3$EXT
  $IS_WIN || chmod +x $BIN/z3
  rm z3.zip
}

install_cvc4() {
  is_exe "$BIN" "cvc4" && return
  version="${CVC4_VERSION#4.}" # 4.y.z -> y.z

  case "$RUNNER_OS" in
    Linux) file="x86_64-linux-opt" ;;
    Windows) file="win64-opt.exe" ;;
    macOS) file="macos-opt" ;;
  esac
  # Temporary workaround
  if [[ "$RUNNER_OS" == "Linux" ]]; then
    curl -o cvc4$EXT -L "https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/unstable/cvc4-2020-08-18-x86_64-linux-opt"
  else
    curl -o cvc4$EXT -L "https://github.com/CVC4/CVC4/releases/download/$version/cvc4-$version-$file"
  fi
  $IS_WIN || chmod +x cvc4$EXT
  mv cvc4$EXT "$BIN/cvc4$EXT"
}

install_yices() {
  is_exe "$BIN" "yices" && return
  ext=".tar.gz"
  case "$RUNNER_OS" in
    Linux) file="pc-linux-gnu-static-gmp.tar.gz" ;;
    macOS) file="apple-darwin18.7.0-static-gmp.tar.gz" ;;
    Windows) file="pc-mingw32-static-gmp.zip" && ext=".zip" ;;
  esac
  curl -o "yices$ext" -L "https://yices.csl.sri.com/releases/$YICES_VERSION/yices-$YICES_VERSION-x86_64-$file"

  if $IS_WIN; then
    7z x -bd "yices$ext"
    mv "yices-$YICES_VERSION"/bin/*.exe "$BIN"
  else
    tar -xzf "yices$ext"
    pushd "yices-$YICES_VERSION" || exit
    sudo ./install-yices
    popd || exit
  fi
  rm -rf "yices$ext" "yices-$YICES_VERSION"
}

configure() {
  ghc_ver="$(ghc --numeric-version)"
  #cp cabal.GHC-"$ghc_ver".config cabal.project.freeze
  cabal v2-update
  cabal v2-configure -j2 --minimize-conflict-set
  #tee -a cabal.project > /dev/null < cabal.project.ci
}

build() {
  if ! retry cabal v2-build "$@" && [[ "$RUNNER_OS" == "macOS" ]]; then
    echo "Working around a dylib issue on macos by removing the cache and trying again"
    cabal v2-clean
    retry cabal v2-build "$@"
  fi
}

test() {
  # System-agnostic path
  export PATH="$PATH:/usr/local/opt/llvm/bin:/c/Program Files/LLVM/bin"
  ${CLANG:-:} --version || echo clang version unknown
  ${LLVM_LINK:-:} --version || echo llvm_link version unknown
  cabal v2-test "$@"
}

install_llvm() {
  if [[ "$RUNNER_OS" = "Linux" ]]; then
    sudo apt-get update -q && sudo apt-get install -y clang-10 llvm-10-tools
  elif [[ "$RUNNER_OS" = "macOS" ]]; then
    brew install llvm@11
  elif [[ "$RUNNER_OS" = "Windows" ]]; then
    choco install llvm
  else
    echo "Unknown platform!"
    return 1
  fi
}

install_system_deps() {
  install_z3
  # install_cvc4 &
  install_yices
  install_llvm
  # wait
  export PATH=$PWD/$BIN:$PATH
  echo "$PWD/$BIN" >> $GITHUB_PATH
  is_exe "$BIN" z3 && is_exe "$BIN" yices
}

sign() {
  set +x
  gpg --yes --quiet --batch --import <(echo "$SIGNING_KEY")
  fingerprint="$(gpg --list-keys | grep galois -a1 | head -n1 | awk '{$1=$1};1')"
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
  pkgname="${pkgname:-"$1-$VERSION-$OS_TAG-x86_64"}"
  mv dist "$pkgname"
  tar -czf "$pkgname".tar.gz "$pkgname"
  sign "$pkgname".tar.gz
  [[ -f "$pkgname".tar.gz.sig ]] && [[ -f "$pkgname".tar.gz ]]
  rm -rf dist
}

bundle_crux_llvm_files() {
  setup_dist
  extract_exe crux-llvm dist/bin
  if ! $IS_WIN; then
    extract_exe crux-llvm-svcomp dist/bin
  fi
  cp crux-llvm/README.md dist/doc
  cp -r crux-llvm/c-src dist
  VERSION=${VERSION:-$DATE}
  zip_dist crux-llvm
}

bundle_crux_mir_files() {
  setup_dist
  extract_exe crux-mir dist/bin
  cp crux-mir/README.md dist/doc
  cp -r crux-mir/rlibs dist
  (cd dependencies/mir-json && cargo install --locked --force --root ../../dist)
  VERSION=${VERSION:-$DATE}
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
