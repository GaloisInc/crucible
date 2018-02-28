struct S(u32);

trait T {
    fn g(&self) -> u32;
}

impl T for S {
    fn g(&self) -> u32 { self.0 }
}

fn f(s: S) -> u32 {
    s.g()
}

const ARG: S = S(42);

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
