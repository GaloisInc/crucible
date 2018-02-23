fn f(x: bool) -> bool {
    x ^ true
}

const ARG: bool = true;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
