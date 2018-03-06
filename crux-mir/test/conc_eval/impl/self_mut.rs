struct S {
    x: u32,
}

impl S {
    fn g(&mut self) {
        self.x += 1;
    }
}

fn f(_: ()) -> u32 {
    let mut s = S { x: 41 };
    s.g();
    s.x
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
