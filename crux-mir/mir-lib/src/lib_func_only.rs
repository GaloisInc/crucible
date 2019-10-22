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

#![stable(feature = "rust1", since = "1.0.0")]

pub mod ops {
    #![stable(feature = "rust1", since = "1.0.0")]

    mod function;
    #[stable(feature = "rust1", since = "1.0.0")]
    pub use self::function::*;
}
