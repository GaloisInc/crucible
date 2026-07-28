//! This test checks that we can correctly write `MirAggregate`s to a reference
//! with an `Empty_RefPath` that already contains a larger aggregate.

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [u8; 2] {
    let mut arr2: [u8; 2] = [42, 84];
    let arr1_ref: &mut [u8; 1] = unsafe { std::mem::transmute(&mut arr2) };
    *arr1_ref = [0];
    // Check that `arr2[0]` was overwritten and `arr2[1]` was not.
    assert_eq!(arr2[0], 0);
    assert_eq!(arr2[1], 84);
    arr2[1] = 1;
    assert_eq!(arr2[0], 0);
    assert_eq!(arr2[1], 1);
    arr2
}

pub fn main() {
    println!("{:?}", crux_test())
}
