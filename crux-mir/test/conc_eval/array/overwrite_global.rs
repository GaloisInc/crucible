//! This test checks that we can correctly write `MirAggregate`s to a reference
//! with an `Empty_RefPath` that already contains a larger aggregate.

static mut ARR2: [u8; 2] = [42u8; 2];

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [u8; 2] {
    let arr1_ref: &mut [u8; 1] = unsafe { std::mem::transmute(&mut ARR2) };
    *arr1_ref = [0];
    unsafe { ARR2[1] = 1 };
    assert_eq!(unsafe { ARR2[0] }, 0);
    assert_eq!(unsafe { ARR2[1] }, 1);
    unsafe { ARR2 }
}

pub fn main() {
    println!("{:?}", crux_test())
}
