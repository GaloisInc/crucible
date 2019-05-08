fn f(x: usize) -> bool {
    let s = b"hello";
    s.len() > x
}

const ARG: usize = 2;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
