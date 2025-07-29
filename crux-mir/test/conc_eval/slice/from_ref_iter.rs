// FAIL: pointer arithmetic on a non-array

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let foo: i32 = 42;
    let foo_slice: &[i32] = core::slice::from_ref(&foo);

    let mut res: i32 = 0;
    for i in foo_slice.iter() {
        res += i;
    }

    assert_eq!(res, 42);
    res
}

fn main() {
    println!("{:?}", crux_test());
}
