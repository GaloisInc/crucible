fn f(x: u8) -> u8 {
    x + 1
}

const ARG: u8 = 1;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
