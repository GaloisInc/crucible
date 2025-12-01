use std::cmp::Ordering;

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> Ordering {
    1.cmp(&2)
}

pub fn main() { println!("{:?}", crux_test()); }
