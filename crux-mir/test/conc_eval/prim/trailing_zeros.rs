// A regression test for #1689.
//
// `trailing_zeros` (implemented for primitive integer types) is implemented in
// terms of the `cttz` intrinsic, so this test case does some basic validation
// of crucible-mir's custom override for this intrinsic.
macro_rules! trailing_zeros_tests {
    ($($ty:ty,)*) => {
        $(
            let n: $ty = 40;
            assert_eq!(n.trailing_zeros(), 3);

            let zero: $ty = 0;
            assert_eq!(zero.trailing_zeros(), (size_of::<$ty>() as u32) * 8);

            let max = <$ty>::MAX;
            assert_eq!(max.trailing_zeros(), 0);
        )*
    }
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    trailing_zeros_tests! {
        u8, u16, u32, u64, u128, usize,
    };
}

pub fn main() {
    println!("{:?}", crux_test());
}
