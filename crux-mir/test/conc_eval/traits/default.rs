// FAIL: default implementation ignored

// Test trait with default implementation
//
// See https://github.com/GaloisInc/mir-json/issues/8

trait T {
    fn m (&self) -> i32;

    fn g (&self) -> i32 { 42 }
}


impl T for i32 {
    fn m (&self) -> i32 { *self }
}

fn f(x : i32) -> i32 {
    x.m()
}

const ARG: i32 = 12;

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
