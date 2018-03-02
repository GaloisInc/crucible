fn f(x: i64) -> i64 {
    x << 63u8
}

const ARG: i64 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
