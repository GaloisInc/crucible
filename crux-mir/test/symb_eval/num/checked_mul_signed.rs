#[cfg_attr(crux, crux_test)]
fn crux_test() -> i8 {
    let x = -3;
    -100 * x
}

pub fn main() {
    println!("{:?}", crux_test());
}
