// A regression test for #1451. This tests the rotate_{left,right} intrinsics
// at various, commonly-encountered bit widths to ensure that translation
// succeeds and behaves as expected.

macro_rules! rol_test {
    ($name:ident, $ty:ty) => {
        pub fn $name() {
            let n: $ty = 3;
            let expected = 12;
            let actual = n.rotate_left(2);
            assert!(expected == actual);
        }
    }
}

macro_rules! ror_test {
    ($name:ident, $ty:ty) => {
        pub fn $name() {
            let n: $ty = 12;
            let expected = 3;
            let actual = n.rotate_right(2);
            assert!(expected == actual);
        }
    }
}

rol_test!(i8_rol_test, i8);
rol_test!(i16_rol_test, i16);
rol_test!(i32_rol_test, i32);
rol_test!(i64_rol_test, i64);
rol_test!(i128_rol_test, i128);
rol_test!(isize_rol_test, isize);

ror_test!(i8_ror_test, i8);
ror_test!(i16_ror_test, i16);
ror_test!(i32_ror_test, i32);
ror_test!(i64_ror_test, i64);
ror_test!(i128_ror_test, i128);
ror_test!(isize_ror_test, isize);

rol_test!(u8_rol_test, u8);
rol_test!(u16_rol_test, u16);
rol_test!(u32_rol_test, u32);
rol_test!(u64_rol_test, u64);
rol_test!(u128_rol_test, u128);
rol_test!(usize_rol_test, usize);

ror_test!(u8_ror_test, u8);
ror_test!(u16_ror_test, u16);
ror_test!(u32_ror_test, u32);
ror_test!(u64_ror_test, u64);
ror_test!(u128_ror_test, u128);
ror_test!(usize_ror_test, usize);

#[cfg_attr(crux, crux::test)]
pub fn rol_ror_tests() {
    i8_rol_test();
    i16_rol_test();
    i32_rol_test();
    i64_rol_test();
    i128_rol_test();
    isize_rol_test();

    i8_ror_test();
    i16_ror_test();
    i32_ror_test();
    i64_ror_test();
    i128_ror_test();
    isize_ror_test();

    u8_rol_test();
    u16_rol_test();
    u32_rol_test();
    u64_rol_test();
    u128_rol_test();
    usize_rol_test();

    u8_ror_test();
    u16_ror_test();
    u32_ror_test();
    u64_ror_test();
    u128_ror_test();
    usize_ror_test();
}

pub fn main() {
    println!("{:?}", rol_ror_tests());
}
