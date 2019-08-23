//! Dummy crate to satisfy injected `compiler_buitins` import.  The functions provided by the real
//! `libcompiler_builtins` are used at a lower level than `crux-mir` deals with.
#![crate_type = "rlib"]
#![crate_name = "compiler_builtins"]
// `no_core` prevents the `compiler_builtins` import from being injected into this crate.  rustc
// also recognizes a `no_builtins` attribute, but it doesn't seem to do anything.
#![feature(no_core)]
#![no_core]
