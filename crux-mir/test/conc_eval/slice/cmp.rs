// A regression test which ensures that crucible-mir can simulate inequality
// operations (i.e., `PartialCmp` methods) over numeric slices. Among other
// things, this requires patching mir-json's standard libraries to avoid
// extra-fancy `transmute`s in slices' `PartialCmp` impls (see
// https://github.com/GaloisInc/mir-json/issues/340) and defining a custom
// override for the `compare_bytes` intrinsic (see
// https://github.com/GaloisInc/crucible/issues/1921).

macro_rules! test_slice_cmp {
    ($ty:ty) => {
        let x0: &[$ty] = &[];

        // Self-comparison
        assert!(!(x0 < x0));
        assert!(x0 <= x0);
        assert!(!(x0 > x0));
        assert!(x0 >= x0);

        let x1a: &[$ty] = &[0];
        let x1b: &[$ty] = &[1];

        // Self-comparison
        assert!(!(x1a < x1a));
        assert!(x1a <= x1a);
        assert!(!(x1a > x1a));
        assert!(x1a >= x1a);

        // Comparison to different slice of same length
        assert!(x1a < x1b);
        assert!(x1a <= x1b);
        assert!(!(x1a > x1b));
        assert!(!(x1a >= x1b));

        // Comparison to slice of different length
        assert!(x0 < x1a);
        assert!(x0 <= x1a);
        assert!(!(x0 > x1a));
        assert!(!(x0 >= x1a));

        let x2a: &[$ty] = &[0, 0];
        let x2b: &[$ty] = &[0, 1];

        // Self-comparison
        assert!(!(x2a < x2a));
        assert!(x2a <= x2a);
        assert!(!(x2a > x2a));
        assert!(x2a >= x2a);

        // Comparison to different slice of same length
        assert!(x2a < x2b);
        assert!(x2a <= x2b);
        assert!(!(x2a > x2b));
        assert!(!(x2a >= x2b));

        // Comparison to slice of different length
        assert!(x1a < x2a);
        assert!(x1a <= x2a);
        assert!(!(x1a > x2a));
        assert!(!(x1a >= x2a));

        assert!(x1b > x2a);
        assert!(x1b >= x2a);
        assert!(!(x1b < x2a));
        assert!(!(x1b <= x2a));
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    test_slice_cmp!(u8);
    test_slice_cmp!(u16);
    test_slice_cmp!(u32);
    test_slice_cmp!(u64);
    test_slice_cmp!(u128);
    test_slice_cmp!(usize);
    test_slice_cmp!(i8);
    test_slice_cmp!(i16);
    test_slice_cmp!(i32);
    test_slice_cmp!(i64);
    test_slice_cmp!(i128);
    test_slice_cmp!(isize);
}

fn main() {
    println!("{:?}", crux_test());
}
