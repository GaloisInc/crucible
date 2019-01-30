// FAIL: can't match up the impls for the traits with their types
//
// We match the type of S::g against T::g.  But g's type
// does not include 'Self' so there is no information to be gained.
//
// We need more info from mir-json to make progress: Issue #4
//

enum S {}

trait T {
    fn g() -> u32;
}

impl T for S {
    fn g() -> u32 { 42 }
}

fn f(_: ()) -> u32 {
    S::g()
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
