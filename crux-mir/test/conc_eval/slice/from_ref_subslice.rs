// FAIL: pointer arithmetic on a non-array

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let foo: i32 = 42;
    let foo_slice: &[i32] = core::slice::from_ref(&foo);

    let foo_subslice = &foo_slice[1..];
    assert!(foo_subslice.is_empty());
}

fn main() {
    println!("{:?}", crux_test());
}
