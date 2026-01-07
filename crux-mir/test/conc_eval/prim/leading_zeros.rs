// `leading_zeros` (implemented for primitive integer types) is implemented in
// terms of the `ctlz` intrinsic, so this test case does some basic validation
// of crucible-mir's custom override for this intrinsic.
macro_rules! leading_zeros_tests {
    ($($ty:ty,)*) => {
        $(
            let n = <$ty>::MAX >> 2;
            assert_eq!(n.leading_zeros(), 2);

            let zero: $ty = 0;
            assert_eq!(zero.leading_zeros(), (size_of::<$ty>() as u32) * 8);

            let max = <$ty>::MAX;
            assert_eq!(max.leading_zeros(), 0);
        )*
    }
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    leading_zeros_tests! {
        u8, u16, u32, u64, u128, usize,
    };
}

pub fn main() {
    println!("{:?}", crux_test());
}
