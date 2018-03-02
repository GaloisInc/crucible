enum E {
    A(u8),
    B(i32),
}

fn f(_: ()) -> u8 {
    let x = E::A(42);
    match x {
        E::A(n) => n,
        E::B(n) => 0,
    }
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
