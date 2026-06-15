use std::any::TypeId;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (bool, bool) {
    let x = TypeId::of::<i32>();
    let y = TypeId::of::<i32>();
    let z = TypeId::of::<u32>();
    (x == y, x != z)
}

pub fn main() {
    println!("{:?}", crux_test());
}
