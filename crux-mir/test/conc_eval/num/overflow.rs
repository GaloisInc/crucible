use std::collections::VecDeque;

#[cfg_attr(crux, crux_test)]
fn crux_test() {
    assert!(1_u8.overflowing_add(2) == (3, false));
    assert!(255_u8.overflowing_add(2) == (1, true));
    assert!(2_u8.overflowing_sub(1) == (1, false));
    assert!(1_u8.overflowing_sub(2) == (255, true));

    assert!(1_i8.overflowing_add(2) == (3, false));
    assert!(126_i8.overflowing_add(2) == (-128, true));
    assert!(2_i8.overflowing_sub(1) == (1, false));
    assert!((-127_i8).overflowing_sub(2) == (127, true));
}

pub fn main() {
    println!("{:?}", crux_test());
}
