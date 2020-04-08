#![cfg_attr(not(with_main), no_std)]
extern crate core;
pub mod def {
    use core::marker::Sized;

    pub trait Def: Sized {
        fn def() -> Self;
    }

     macro_rules! default_impl {
        ($t:ty, $v:expr, $doc:tt) => {
            impl Def for $t {
                #[inline]
                #[doc = $doc]
                fn def() -> $t { $v }
            }
        }
     }
    default_impl! { (), (), "Returns the default value of `()`" }    
    impl Def for u8 {
        #[inline]
        #[doc = "Returns default value of `0`"]
        fn def() -> u8 { 0 }
    } 

}

use def::Def;

fn f(_x : i32) -> () {
    return Def::def()
}

const ARG : i32 = 0;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> () { f(ARG) }
