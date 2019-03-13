// Fail: Cannot assign to atom: "_1" of type [u8; 4]

// parameter is mutable in Rust, so we should make a local variable on translation

fn h(mut x: [u8; 4]) -> [u8; 4] {
    x[0] = 42;
    x
}


fn f(x:u8) -> u8 {
    let mut y = [0;4];
    y[0] = x;
    h(y);
    y[0]
}


const ARG: u8 = 2;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
