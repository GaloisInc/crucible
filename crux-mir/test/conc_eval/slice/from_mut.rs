#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let mut foo: i32 = 42;
    let mut foo_slice: &mut [i32] = core::slice::from_mut(&mut foo);
    foo_slice[0] = 43;
    assert!(foo == 43);
    foo
}

fn main() {
    println!("{:?}", crux_test());
}
