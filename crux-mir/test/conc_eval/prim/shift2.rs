fn f(x: u8) -> u8 {
    x << 1i32
}

const ARG: u8 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
