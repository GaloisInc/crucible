#![crate_type = "lib"]
#![no_std]
#![feature(core_intrinsics)]
#![feature(doc_alias)]
#![feature(exact_size_is_empty)]
#![feature(i128_type)]
#![feature(lang_items)]
#![feature(never_type)]
#![feature(on_unimplemented)]
#![feature(rustc_attrs)]
#![feature(rustc_const_unstable)]
#![feature(specialization)]
#![feature(staged_api)]
#![feature(trusted_len)]
#![feature(try_trait)]
#![feature(untagged_unions)]
#![feature(fundamental)]
#![feature(pin)]
#![feature(coerce_unsized)]
#![feature(unsize)]


#![stable(feature = "rust1", since = "1.0.0")]

#[macro_use] mod internal_macros;

pub mod clone;
pub mod cmp;
pub mod convert;
pub mod default;
pub mod ops;
pub mod option;
pub mod result;
pub mod slice;
pub mod pin;
