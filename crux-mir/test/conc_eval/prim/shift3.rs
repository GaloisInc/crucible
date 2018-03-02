fn f(x: i64) -> i64 {
    x << 63i64
}

const ARG: i64 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
