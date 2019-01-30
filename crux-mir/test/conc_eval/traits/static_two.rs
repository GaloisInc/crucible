// FAIL: can't match up the impls for the traits with their types
//
// Test two static implementation of the same trait
//
// We match the type of S::g and U::g against T::g.  But g's type
// does not include 'Self' so there is no information to be gained.
//
// We need more info from mir-json to make progress: Issue #4



enum S {}
enum U {}

trait T {
    fn g() -> u32;
}

impl T for S {
    fn g() -> u32 { 42 }
}

impl T for U {
    fn g() -> u32 { 1 }
}

fn f(_: ()) -> u32 {
    U::g()
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
