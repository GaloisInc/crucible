#!/bin/sh
set -e

compile() {
    compile_2015 --edition 2018 "$@"
}

compile_2015() {
    rustc -L rlibs_native --out-dir rlibs_native --crate-type rlib "$@"
}

translate() {
    translate_2015 --edition 2018 "$@"
}

translate_2015() {
    mir-json -L rlibs --out-dir rlibs --crate-type rlib "$@"
}


translate lib/libcore/lib.rs --crate-name core \
    --cfg iter_count --cfg iter_last --cfg iter_min_max \
    --cfg ascii --cfg char --cfg unicode \
    --cfg slice_sort \
    --cfg time --cfg simd --cfg sync

    #--cfg slice_u8 
    #--cfg str #--cfg str_lossy --cfg memchr --cfg str_pattern

translate lib/compiler_builtins.rs --cfg 'feature="compiler-builtins"' --cfg stage0
translate lib/crucible/lib.rs --crate-name crucible
translate lib/int512.rs
translate lib/std/lib.rs --crate-name std --cfg 'feature="std"'
translate_2015 lib/byteorder/lib.rs --crate-name byteorder --cfg 'feature="std"'
translate lib/bytes.rs

# Need native versions of some libs for conc_eval oracle programs
compile_2015 lib/byteorder/lib.rs --crate-name byteorder --cfg 'feature="std"'
