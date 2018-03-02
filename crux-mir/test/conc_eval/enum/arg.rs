enum E {
    A(u8),
    B(i32),
}

fn f(x: E) -> u8 {
    match x {
        E::A(n) => n,
        E::B(n) => 0,
    }
}

const ARG: E = E::A(42);

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
