#![cfg_attr(not(with_main), no_std)]
// a static trait invocation for a polymorphic type
// calling the g method in h requires a dictionary argument
// Furthermore the impl for this dictionary argument is generic
// so the dictionary needs to satisfy constraints itself

struct Data<T>(T);

trait G {
    fn g (&self) -> u32;
}

impl G for u32 {
    fn g(&self) -> u32 {
        return 1
    }
}

impl <T:G> G for Data<T> {
    fn g(&self) -> u32 {
        let x = &self.0;
        self.0.g()
    }
}


fn h<T>(x:T) -> u32 where T:G {
    x.g()
}

fn f(_: ()) -> u32 {
    let d = Data(32);
    let e = Data(d.0);
    e.g()
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> u32 { f(ARG) }
