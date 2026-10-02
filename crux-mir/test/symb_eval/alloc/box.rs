extern crate crucible;
use crucible::Symbolic;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let b = Box::<i32>::symbolic("b");
    (*b).wrapping_add(1)
}

pub fn main() {
    println!("{:?}", crux_test());
}
