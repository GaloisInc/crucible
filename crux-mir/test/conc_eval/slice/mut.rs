fn g(xs: &mut [u8], v: u8) -> () {
    xs[0] = v;
}

fn f(x: u8) -> u8 {
    let mut xs = [0; 4];
    g(&mut xs, x);
    xs[0]
}

const ARG: u8 = 42;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
