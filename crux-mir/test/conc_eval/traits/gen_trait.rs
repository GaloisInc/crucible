#![cfg_attr(not(with_main), no_std)]
// a static trait invocation for a polymorphic type
// calling the g method in h requires a dictionary argument

trait G<U> {
    fn g (&self,y:U) -> U;
}

trait T {
    fn t<U> (&self, y:U) -> U;
}

trait S {
    type A;
    fn s (&self, y:Self::A) -> Self::A;
}

impl G<i32> for u32 {
    fn g (&self, y:i32) -> i32 { y }
}
impl T for u32 {
    fn t<U>(&self, y:U) -> U { y }
}
impl S for u32 {
    type A = i32;
    fn s(&self,y:i32) -> i32 { y }
}

fn f(_: ()) -> i32 {
    let y : i32 = -23;
    let x : u32 = 12;
    x.g(y) + x.t(y) + x.s(y)
}


const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> i32 { f(ARG) }
