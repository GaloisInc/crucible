#![crate_type = "lib"]
#![crate_name = "core"]
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

#![feature(doc_spotlight)]
#![feature(non_exhaustive)]
#![feature(no_panic_pow)]
#![feature(reverse_bits)]
#![feature(wrapping_next_power_of_two)]
#![feature(const_int_sign)]
#![feature(const_int_conversion)]


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

/*
#[path = "num/int_macros.rs"]
#[macro_use]
mod int_macros;

#[path = "num/uint_macros.rs"]
#[macro_use]
mod uint_macros;

#[path = "num/isize.rs"] pub mod isize;
#[path = "num/i8.rs"]    pub mod i8;
#[path = "num/i16.rs"]   pub mod i16;
#[path = "num/i32.rs"]   pub mod i32;
#[path = "num/i64.rs"]   pub mod i64;
#[path = "num/i128.rs"]  pub mod i128;

#[path = "num/usize.rs"] pub mod usize;
#[path = "num/u8.rs"]    pub mod u8;
#[path = "num/u16.rs"]   pub mod u16;
#[path = "num/u32.rs"]   pub mod u32;
#[path = "num/u64.rs"]   pub mod u64;
#[path = "num/u128.rs"]  pub mod u128;

#[path = "num/f32.rs"]   pub mod f32;
#[path = "num/f64.rs"]   pub mod f64;

#[macro_use]
pub mod num;
*/




