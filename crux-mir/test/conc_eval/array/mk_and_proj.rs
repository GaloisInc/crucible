fn f(x: u8) -> u8 {
    let xs = [x; 4];
    xs[0]
}

const ARG: u8 = 42;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
