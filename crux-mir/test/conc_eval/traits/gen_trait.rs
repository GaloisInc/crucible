// FAIL: needs a polymorphic member in the dictionary for T

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
fn main() {
   println!("{:?}", f(ARG));
}
