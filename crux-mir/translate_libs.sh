#!/bin/sh
set -e

compile() {
    compile --edition 2018 "$@"
}

compile_2015() {
    rustc -L rlibs_native --out-dir rlibs_native --crate-type rlib "$@"
}

translate() {
    translate --edition 2018 "$@"
}

translate_2015() {
    mir-json -L rlibs --out-dir rlibs --crate-type rlib "$@"
}


translate lib/libcore/lib.rs --crate-name core
translate lib/compiler_builtins.rs --cfg 'feature="compiler-builtins"' --cfg stage0
translate lib/crucible.rs
translate lib/int512.rs
translate lib/std/lib.rs --crate-name std --cfg 'feature="std"'
translate_2015 lib/byteorder/lib.rs --crate-name byteorder --cfg 'feature="std"'

# Need native versions of some libs for conc_eval oracle programs
compile_2015 lib/byteorder/lib.rs --crate-name byteorder --cfg 'feature="std"'
