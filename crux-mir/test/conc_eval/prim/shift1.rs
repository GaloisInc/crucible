fn f(x: u8) -> u8 {
    x << 1u8
}

const ARG: u8 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
