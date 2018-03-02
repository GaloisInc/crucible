fn g(xs: &[u8]) -> u8 {
    xs[0]
}

fn f(x: u8) -> u8 {
    let xs = [x; 4];
    g(&xs)
}

const ARG: u8 = 42;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
