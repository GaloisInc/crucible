// A regression test for #1873. This tests crucible-mir's ability to support
// float-related `as` casts.

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    ///// casting from a float to an integer
    assert_eq!(42.9f32 as i32, 42);
    assert_eq!(42.9f32 as u32, 42);

    assert_eq!(-42.9f32 as i32, -42);
    assert_eq!(-42.9f32 as u32, u32::MIN);

    assert_eq!(f32::NAN as i32, 0);
    assert_eq!(f32::NAN as u32, 0);

    assert_eq!(-1_000_000_000_000_000f32 as i32, i32::MIN);
    assert_eq!(-1_000_000_000_000_000f32 as u32, u32::MIN);

    assert_eq!(1_000_000_000_000_000f32 as i32, i32::MAX);
    assert_eq!(1_000_000_000_000_000f32 as u32, u32::MAX);

    assert_eq!(f32::NEG_INFINITY as i32, i32::MIN);
    assert_eq!(f32::NEG_INFINITY as u32, u32::MIN);

    assert_eq!(f32::INFINITY as i32, i32::MAX);
    assert_eq!(f32::INFINITY as u32, u32::MAX);

    ///// casting from an integer to a float
    assert_eq!(0u32 as f32, 0.0f32);
    assert_eq!(0i32 as f32, 0.0f32);

    assert_eq!(1u32 as f32, 1.0f32);
    assert_eq!(1i32 as f32, 1.0f32);

    assert_eq!(-1i32 as f32, -1.0f32);

    ///// casting from a float to a wider float
    assert!((f32::NAN as f64).is_nan());
    assert_eq!(1.0f32 as f64, 1.0f64);
    assert_eq!(0.0f32 as f64, 0.0f64);
    assert_eq!(-0.0f32 as f64, -0.0f64);
    assert_eq!(-1.0f32 as f64, -1.0f64);
    assert_eq!(f32::NEG_INFINITY as f64, f64::NEG_INFINITY);
    assert_eq!(f32::INFINITY as f64, f64::INFINITY);

    ///// casting from a float to a narrower float
    assert!((f64::NAN as f32).is_nan());
    assert_eq!(1.0f64 as f32, 1.0f32);
    assert_eq!(0.0f64 as f32, 0.0f32);
    assert_eq!(-0.0f64 as f32, -0.0f32);
    assert_eq!(-1.0f64 as f32, -1.0f32);
    assert_eq!(f64::NEG_INFINITY as f32, f32::NEG_INFINITY);
    assert_eq!(f64::INFINITY as f32, f32::INFINITY);
}

pub fn main() {
    println!("{:?}", crux_test());
}
