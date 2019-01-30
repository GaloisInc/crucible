// Fail: Cannot assign to atom: "_1" of type [u8; 4]

// parameter is mutable in Rust, so we should make a local variable on translation

fn f(mut x: [u8; 4]) -> [u8; 4] {
    x[0] = 42;
    x
}

const ARG: [u8; 4] = [0; 4];

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
