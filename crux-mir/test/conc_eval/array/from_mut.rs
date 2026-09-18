#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let mut foo: i32 = 42;
    let foo_array: &mut [i32; 1] = core::array::from_mut(&mut foo);
    foo_array[0] = 43;
    assert!(foo == 43);
    foo
}

fn main() {
    println!("{:?}", crux_test());
}
