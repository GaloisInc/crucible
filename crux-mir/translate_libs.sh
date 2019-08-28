#!/bin/sh
set -e

translate() {
    mir-json -L rlibs --out-dir rlibs --edition 2018 --crate-type rlib "$@"
}

translate lib/libcore/lib.rs --crate-name core
translate lib/compiler_builtins.rs --cfg 'feature="compiler-builtins"' --cfg stage0
translate lib/crucible.rs
translate lib/int512.rs
translate lib/std/lib.rs --crate-name std
