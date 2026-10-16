#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let foo: i32 = 42;
    let foo_array: &[i32; 1] = core::array::from_ref(&foo);
    foo_array[0]
}

fn main() {
    println!("{:?}", crux_test());
}
