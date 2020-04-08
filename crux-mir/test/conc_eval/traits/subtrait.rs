#![cfg_attr(not(with_main), no_std)]
trait A {
    fn a(&self) -> u32;
}
trait B : A {
    fn b(&self) -> u32;
}

struct Data(u32);

impl A for Data {
    fn a(&self) -> u32 { self.0 + 41 }
}
impl B for Data {
    fn b(&self) -> u32 { self.0 + self.a() }
}

fn g<T>(x : T) -> u32 where T : B {
    x.a()
}

fn f(_: ()) -> u32 {
    let d = Data(32);
    g (d)
}


const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> u32 { f(ARG) }
