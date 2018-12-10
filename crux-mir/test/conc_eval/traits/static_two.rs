// FAIL: Wrong invocation (see file for details)
// Test two static implementation of the same trait
//
// This test currently fails because mir-json calls the 
// S version {{impl}}[0]::g[0] and the
// U version {{impl}}[1]::g[0].
//
// However, the invocation in f is to T[0]::g[0]


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
