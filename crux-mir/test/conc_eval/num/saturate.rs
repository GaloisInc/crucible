use std::collections::VecDeque;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    assert_eq!(1_u8.saturating_add(2), 3);
    assert_eq!(254_u8.saturating_add(2), 255);
    assert_eq!(2_u8.saturating_sub(1), 1);
    assert_eq!(1_u8.saturating_sub(2), 0);

    assert!(1_i8.saturating_add(2) == 3);
    assert!(126_i8.saturating_add(2) == 127);
    assert!(2_i8.saturating_sub(1) == 1);
    assert!((-127_i8).saturating_sub(2) == -128);
}

pub fn main() {
    println!("{:?}", crux_test());
}
