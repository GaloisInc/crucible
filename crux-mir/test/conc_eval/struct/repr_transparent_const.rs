use std::num::Wrapping;

static W: Wrapping<i32> = Wrapping(123);

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    (W + Wrapping(1)).0
}

pub fn main() {
    println!("{:?}", crux_test());
}
