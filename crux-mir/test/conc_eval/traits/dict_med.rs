#![cfg_attr(not(with_main), no_std)]
// a static trait invocation for a polymorphic type
// calling the g method in h requires a dictionary argument 

struct Data<T>(T);

trait G<U> {
    fn g (&self) -> U;
}


impl G<u32> for u32 {
    fn g(&self) -> u32 {
        42
    }
}

impl<U> G<u32> for Data<U> where U:G<u32> {
    fn g(&self) -> u32 {
        (self.0).g()
    }
}


fn f(_: ()) -> u32 {
    let d = Data(32);
    d.g()
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
