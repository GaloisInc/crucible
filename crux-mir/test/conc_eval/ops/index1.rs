use std::ops::Index;

struct S;

impl Index<u32> for S {
    type Output = S;
    fn index(&self, idx: u32) -> &S {
        static THE_S: S = S;
        &THE_S
    }
}

const ARG: i32 = 1;
fn f(arg: i32) {
}

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
