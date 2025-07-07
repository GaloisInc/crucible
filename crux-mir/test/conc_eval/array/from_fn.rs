use std::array;

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> [usize; 3] {
    array::from_fn(|i| i)
}

pub fn main() {
    println!("{:?}", crux_test());
}
