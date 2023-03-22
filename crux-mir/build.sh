set -e

export STD_ENV_ARCH=$(uname -m)

echo 'Building core...'
mir-json lib/core/src/lib.rs --edition=2021 --crate-name core -L rlibs --out-dir rlibs --crate-type rlib

echo 'Building rustc_std_workspace_core...'
mir-json lib/rustc_std_workspace_core/lib.rs --edition=2021 --crate-name rustc_std_workspace_core -L rlibs --out-dir rlibs --crate-type rlib --extern core=rlibs/libcore.rlib

echo 'Building libc...'
mir-json lib/libc/src/lib.rs  --crate-name libc -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="align"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="rustc-std-workspace-core"' --cfg freebsd11 --cfg libc_priv_mod_use --cfg libc_union --cfg libc_const_size_of --cfg libc_align --cfg libc_int128 --cfg libc_core_cvoid --cfg libc_packedN --cfg libc_cfg_target_vendor --cfg libc_non_exhaustive --cfg libc_ptr_addr_of --cfg libc_underscore_const_names --cfg libc_thread_local --cfg 'libc_const_extern_fn`' --extern rustc_std_workspace_core=rlibs/librustc_std_workspace_core.rlib

echo 'Building compiler_builtins...'
mir-json lib/compiler_builtins/src/lib.rs  --crate-name compiler_builtins -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="compiler-builtins"' --cfg 'feature="core"' --cfg 'feature="default"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="unstable"' --cfg 'feature="mem-unaligned"`' --extern core=rlibs/libcore.rlib

echo 'Building alloc...'
mir-json lib/alloc/src/lib.rs --edition=2021 --crate-name alloc -L rlibs --out-dir rlibs --crate-type rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib

echo 'Building cfg_if...'
mir-json lib/cfg_if/src/lib.rs --edition=2018 --crate-name cfg_if -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib

echo 'Building memchr...'
mir-json lib/memchr/src/lib.rs --edition=2018 --crate-name memchr -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --cfg memchr_runtime_simd --cfg memchr_runtime_sse2 --cfg memchr_runtime_sse42 --cfg 'memchr_runtime_avx`' --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib

echo 'Building adler...'
mir-json lib/adler/src/lib.rs  --crate-name adler -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib

echo 'Building rustc_demangle...'
mir-json lib/rustc_demangle/src/lib.rs  --crate-name rustc_demangle -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib

echo 'Building unwind...'
mir-json lib/unwind/src/lib.rs --edition=2021 --crate-name unwind -L rlibs --out-dir rlibs --crate-type rlib --extern cfg_if=rlibs/libcfg_if.rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib --extern libc=rlibs/liblibc.rlib

echo 'Building panic_unwind...'
mir-json lib/panic_unwind/src/lib.rs --edition=2021 --crate-name panic_unwind -L rlibs --out-dir rlibs --crate-type rlib --extern alloc=rlibs/liballoc.rlib --extern cfg_if=rlibs/libcfg_if.rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib --extern libc=rlibs/liblibc.rlib --extern unwind=rlibs/libunwind.rlib

echo 'Building rustc_std_workspace_alloc...'
mir-json lib/rustc_std_workspace_alloc/lib.rs --edition=2021 --crate-name rustc_std_workspace_alloc -L rlibs --out-dir rlibs --crate-type rlib --extern alloc=rlibs/liballoc.rlib

echo 'Building panic_abort...'
mir-json lib/panic_abort/src/lib.rs --edition=2021 --crate-name panic_abort -L rlibs --out-dir rlibs --crate-type rlib --extern alloc=rlibs/liballoc.rlib --extern cfg_if=rlibs/libcfg_if.rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib --extern libc=rlibs/liblibc.rlib

echo 'Building gimli...'
mir-json lib/gimli/src/lib.rs --edition=2018 --crate-name gimli -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="read"' --cfg 'feature="read-core"' --cfg 'feature="rustc-dep-of-std"' --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern alloc=rlibs/liballoc.rlib --extern core=rlibs/libcore.rlib

echo 'Building std_detect...'
mir-json lib/std_detect/src/lib.rs --edition=2018 --crate-name std_detect -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="libc"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="std_detect_dlsym_getauxval"' --cfg 'feature="std_detect_file_io"' --extern cfg_if=rlibs/libcfg_if.rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern libc=rlibs/liblibc.rlib --extern alloc=rlibs/liballoc.rlib --extern core=rlibs/libcore.rlib

echo 'Building object...'
mir-json lib/object/src/lib.rs --edition=2018 --crate-name object -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="alloc"' --cfg 'feature="archive"' --cfg 'feature="coff"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="elf"' --cfg 'feature="macho"' --cfg 'feature="pe"' --cfg 'feature="read_core"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="unaligned"' --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern memchr=rlibs/libmemchr.rlib --extern alloc=rlibs/liballoc.rlib --extern core=rlibs/libcore.rlib

echo 'Building miniz_oxide...'
mir-json lib/miniz_oxide/src/lib.rs --edition=2018 --crate-name miniz_oxide -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern adler=rlibs/libadler.rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern alloc=rlibs/liballoc.rlib --extern core=rlibs/libcore.rlib

echo 'Building hashbrown...'
mir-json lib/hashbrown/src/lib.rs --edition=2021 --crate-name hashbrown -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="nightly"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="rustc-internal-api"' --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern alloc=rlibs/liballoc.rlib --extern core=rlibs/libcore.rlib

echo 'Building addr2line...'
mir-json lib/addr2line/src/lib.rs  --crate-name addr2line -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern gimli=rlibs/libgimli.rlib --extern alloc=rlibs/liballoc.rlib --extern core=rlibs/libcore.rlib

echo 'Building std...'
mir-json lib/std/src/lib.rs --edition=2021 --crate-name std -L rlibs --out-dir rlibs --crate-type rlib --cfg 'feature="addr2line"' --cfg 'feature="backtrace"' --cfg 'feature="gimli-symbolize"' --cfg 'feature="miniz_oxide"' --cfg 'feature="object"' --cfg 'feature="panic_unwind"' --cfg 'feature="std_detect_dlsym_getauxval"' --cfg 'feature="std_detect_file_io"' --cfg 'backtrace_in_libstd`' --extern addr2line=rlibs/libaddr2line.rlib --extern alloc=rlibs/liballoc.rlib --extern cfg_if=rlibs/libcfg_if.rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib --extern hashbrown=rlibs/libhashbrown.rlib --extern libc=rlibs/liblibc.rlib --extern miniz_oxide=rlibs/libminiz_oxide.rlib --extern object=rlibs/libobject.rlib --extern panic_abort=rlibs/libpanic_abort.rlib --extern panic_unwind=rlibs/libpanic_unwind.rlib --extern rustc_demangle=rlibs/librustc_demangle.rlib --extern std_detect=rlibs/libstd_detect.rlib --extern unwind=rlibs/libunwind.rlib

echo 'Building proc_macro...'
mir-json lib/proc_macro/src/lib.rs --edition=2021 --crate-name proc_macro -L rlibs --out-dir rlibs --crate-type rlib --extern core=rlibs/libcore.rlib --extern std=rlibs/libstd.rlib

# extra libs (added manually)
echo "Building crucible..."
mir-json lib/crucible/lib.rs --crate-name crucible --edition=2021 -L rlibs --out-dir rlibs --crate-type rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern core=rlibs/libcore.rlib

echo 'Building int512...'
mir-json lib/int512.rs --crate-name int512 -L rlibs --out-dir rlibs --crate-type rlib --extern core=rlibs/libcore.rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib

echo 'Building bytes...'
mir-json lib/bytes.rs --edition=2021 --crate-name bytes -L rlibs --out-dir rlibs --crate-type rlib --extern core=rlibs/libcore.rlib --extern std=rlibs/libstd.rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib --extern crucible=rlibs/libcrucible.rlib

echo 'Building byteorder...'
mir-json lib/byteorder/lib.rs --edition=2021 --crate-name byteorder -L rlibs --out-dir rlibs --crate-type rlib --extern core=rlibs/libcore.rlib --extern std=rlibs/libstd.rlib --extern compiler_builtins=rlibs/libcompiler_builtins.rlib

