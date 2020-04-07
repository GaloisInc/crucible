#![cfg_attr(not(with_main), no_std)]
// a static trait invocation for a polymorphic type
// calling the g method in h requires a dictionary argument 

struct Data<T>(T);

trait G {
    fn g (&self) -> u32;
}

impl G for Data<u32> {
    fn g(&self) -> u32 {
        self.0
    }
}

fn h<T>(x:T) -> u32 where T:G {
    x.g()
}

fn f(_: ()) -> u32 {
    let d = Data(32);
    h(d)
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
