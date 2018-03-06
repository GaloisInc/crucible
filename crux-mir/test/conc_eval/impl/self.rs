struct S {
    x: u32,
}

impl S {
    fn g(&self) -> u32 {
        self.x + 1
    }
}

fn f(_: ()) -> u32 {
    let s = S { x: 41 };
    s.g()
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
