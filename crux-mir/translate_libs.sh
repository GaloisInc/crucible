#!/bin/sh
set -e

compile() {
    compile_2015 --edition 2018 "$@"
}

compile_2015() {
    rustc -L rlibs_native --out-dir rlibs_native --crate-type rlib \
        --remap-path-prefix $PWD=. \
        "$@"
}

translate() {
    translate_2015 --edition 2018 "$@"
}

translate_2015() {
    mir-json -L rlibs --out-dir rlibs --crate-type rlib \
        --remap-path-prefix $PWD=. \
        "$@"
}


translate lib/libcore/lib.rs --crate-name core \
    --cfg 'feature="panic_immediate_abort"' \
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
    --cfg fmt   # trouble with integer formatting in bounds check panics

translate_2015 lib/compiler-builtins/src/lib.rs --crate-name compiler_builtins \
    --cfg 'feature="compiler-builtins"'
translate lib/crucible/lib.rs --crate-name crucible
translate lib/int512.rs
translate lib/liballoc/lib.rs --crate-name alloc \
    --extern crucible
translate lib/cfg-if/src/lib.rs --crate-name cfg_if --cfg 'feature="rustc-dep-of-std"' \
    --extern rustc_std_workspace_core=rlibs/libcore.rlib \
    -ldl
translate_2015 lib/libc/src/lib.rs --crate-name libc \
    --cfg 'feature="rustc-dep-of-std"' --cfg libc_align \
    --extern rustc_std_workspace_core=rlibs/libcore.rlib

if [ "$(uname)" = "Linux" ]; then
    # Under cargo, this flag would be set by libunwind's `build.rs` file.
    libunwind_extra_flags=-lgcc_s
fi
translate lib/libunwind/lib.rs --crate-name unwind \
    --extern cfg_if --extern libc $libunwind_extra_flags

translate lib/libpanic_abort/lib.rs --crate-name panic_abort -C panic=abort \
    --extern libc
translate lib/libpanic_unwind/lib.rs --crate-name panic_unwind -C panic=unwind \
    --extern alloc --extern cfg_if --extern unwind --extern libc
translate lib/hashbrown/src/lib.rs --crate-name hashbrown \
    --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="nightly"' \
    --cfg 'feature="rustc-internal-api"' --cfg has_extern_crate_alloc \
    --extern alloc
translate_2015 lib/rustc-demangle/src/lib.rs --crate-name rustc_demangle \
    --cfg 'feature="rustc-dep-of-std"'
translate_2015 lib/backtrace/crates/backtrace-sys/src/lib.rs --crate-name backtrace_sys
translate lib/backtrace/src/lib.rs --crate-name backtrace \
    --extern core --extern compiler_builtins --extern libc \
    --extern rustc_demangle --extern cfg_if --extern backtrace_sys
translate lib/libstd/lib.rs --crate-name std \
    --cfg 'feature="panic_immediate_abort"' \
    --extern alloc --extern cfg_if \
    --extern hashbrown --extern backtrace_rs=rlibs/libbacktrace.rlib
translate lib/libterm/lib.rs --crate-name term
translate lib/unicode-width/src/lib.rs --crate-name unicode_width \
    --cfg 'feature="rustc-dep-of-std"'
translate lib/getopts/src/lib.rs --crate-name getopts
translate lib/libtest/lib.rs --crate-name test \
    --extern libc  --extern getopts --extern term

translate_2015 lib/byteorder/lib.rs --crate-name byteorder --cfg 'feature="std"'
translate lib/bytes.rs
translate_2015 lib/bigint/src/lib.rs --crate-name bigint

# Need native versions of some libs for conc_eval oracle programs
#compile_2015 lib/byteorder/lib.rs --crate-name byteorder --cfg 'feature="std"'
