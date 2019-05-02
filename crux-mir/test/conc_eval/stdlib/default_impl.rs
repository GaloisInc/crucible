pub mod def {
    use std::marker::Sized;

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
fn main() {
    println!("{:?}", f(ARG))
}
