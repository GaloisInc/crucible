#![feature(i128_type)]
#![crate_type = "lib"]
#![no_implicit_prelude]


pub mod default {
    use std::marker::Sized;
    
    pub trait Default: Sized {
      fn default() -> Self;
    }

    macro_rules! default_impl {
        ($t:ty, $v:expr, $doc:tt) => {
            impl Default for $t {
                #[inline]
                #[doc = $doc]
                fn default() -> $t { $v }
            }
        }
    }


    default_impl! { (), (), "Returns the default value of `()`" }
    default_impl! { bool, false, "Returns the default value of `false`" }
    default_impl! { char, '\x00', "Returns the default value of `\\x00`" }
    
    default_impl! { usize, 0, "Returns the default value of `0`" }
    default_impl! { u8, 0, "Returns the default value of `0`" }
    default_impl! { u16, 0, "Returns the default value of `0`" }
    default_impl! { u32, 0, "Returns the default value of `0`" }
    default_impl! { u64, 0, "Returns the default value of `0`" }
    //default_impl! { u128, 0, "Returns the default value of `0`" }
    

    default_impl! { isize, 0, "Returns the default value of `0`" }
    default_impl! { i8, 0, "Returns the default value of `0`" }
    default_impl! { i16, 0, "Returns the default value of `0`" }
    default_impl! { i32, 0, "Returns the default value of `0`" }
    default_impl! { i64, 0, "Returns the default value of `0`" }
    //default_impl! { i128, 0, "Returns the default value of `0`" }

    //
    // mir-json doesn't handle float literals
    //
    //default_impl! { f32, 0.0f32, "Returns the default value of `0.0`" }
    //default_impl! { f64, 0.0f64, "Returns the default value of `0.0`" }
}
