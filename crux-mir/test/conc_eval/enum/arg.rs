enum E {
    A(u8),
    B(i32,i32),
}

fn f(x: E) -> u8 {
    match x {
        E::A(n) => n,
        E::B(n,m) => 0,
    }
}

const ARG: E = E::B(42,43);

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
