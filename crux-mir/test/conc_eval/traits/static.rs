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
