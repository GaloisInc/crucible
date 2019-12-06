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
    --cfg time --cfg simd --cfg sync \
    --cfg slice_u8 \
    --cfg str --cfg str_lossy --cfg memchr --cfg str_pattern --cfg str_case \
    --cfg flt2dec \
    --cfg from_str --cfg dec2flt \
    --cfg any_downcast \
    --cfg hash \
    # --cfg fmt   # trouble with integer formatting in bounds check panics

translate lib/compiler_builtins.rs --cfg 'feature="compiler-builtins"' --cfg stage0
translate lib/crucible/lib.rs --crate-name crucible
translate lib/int512.rs
translate lib/liballoc/lib.rs --crate-name alloc
translate lib/cfg-if/src/lib.rs --crate-name cfg_if --cfg 'feature="rustc-dep-of-std"' \
    --extern rustc_std_workspace_core=rlibs/libcore.rlib
translate_2015 lib/libc/src/lib.rs --crate-name libc \
    --cfg 'feature="rustc-dep-of-std"' --cfg libc_align \
    --extern rustc_std_workspace_core=rlibs/libcore.rlib
translate lib/libunwind/lib.rs --crate-name unwind \
    --extern cfg_if=rlibs/libcfg_if.rlib \
    --extern libc=rlibs/liblibc.rlib
translate lib/hashbrown/src/lib.rs --crate-name hashbrown \
    --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="nightly"' \
    --extern rustc_std_workspace_core=rlibs/libcore.rlib
translate lib/libstd/lib.rs --crate-name std \
    --extern hashbrown=rlibs/libhashbrown.rlib
translate_2015 lib/byteorder/lib.rs --crate-name byteorder --cfg 'feature="std"'
translate lib/bytes.rs

# Need native versions of some libs for conc_eval oracle programs
#compile_2015 lib/byteorder/lib.rs --crate-name byteorder --cfg 'feature="std"'
