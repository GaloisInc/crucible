fn f(x: u8) -> u8 {
    x / 2
}

const ARG: u8 = 9;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
