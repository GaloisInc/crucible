// FIXME: currently passes, but should fail

#[cfg_attr(crux, crux_test)]
fn crux_test() -> u8 {
    let x = 3;
    100 * x
}

pub fn main() {
    println!("{:?}", crux_test());
}
