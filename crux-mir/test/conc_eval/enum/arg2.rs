enum E {
    #[inline(never)]
    A(u8),
    #[inline(never)]
    B(i32,i32),
}

fn mk3 (y : &mut u8) -> u8 {
    *y = 3;
    0
}

fn f(x: E) -> u8 {
    let y = E::B(23,12);
    match y {
        E::A(n) => n,
        E::B(n,m) => 0,
    }
}

const ARG: E = E::B(42,43);

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
