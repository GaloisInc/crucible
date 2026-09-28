// A regression test for #1872. This exercises various f32 methods that rely on
// transmuting to or from u32s.

use std::cmp::Ordering;
use std::num::FpCategory;

// Minimum representable positive value (min subnormal)
const TINY: f32 = f32::from_bits(0x1);

// An alias for `TINY`. Used in contexts where we want to prominently highlight
// its status as a subnormal floating-point value.
const SUBNORMAL: f32 = TINY;

// An example of a normal (i.e., not subnormal, NaN, zero, or infinite)
// floating-point value.
const NORMAL: f32 = 1.0;

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    ///// classify()
    assert_eq!(f32::NAN.classify(), FpCategory::Nan);
    assert_eq!(f32::INFINITY.classify(), FpCategory::Infinite);
    assert_eq!(f32::NEG_INFINITY.classify(), FpCategory::Infinite);
    assert_eq!(0.0f32.classify(), FpCategory::Zero);
    assert_eq!((-0.0f32).classify(), FpCategory::Zero);
    assert_eq!(SUBNORMAL.classify(), FpCategory::Subnormal);
    assert_eq!((-SUBNORMAL).classify(), FpCategory::Subnormal);
    assert_eq!(NORMAL.classify(), FpCategory::Normal);
    assert_eq!((-NORMAL).classify(), FpCategory::Normal);

    ///// from_bits()
    assert_eq!(f32::from_bits(0x41480000), 12.5f32);

    ///// is_normal()
    assert!(NORMAL.is_normal());
    assert!((-NORMAL).is_normal());

    assert!(!f32::NAN.is_normal());
    assert!(!f32::INFINITY.is_normal());
    assert!(!f32::NEG_INFINITY.is_normal());
    assert!(!0.0f32.is_normal());
    assert!(!(-0.0f32).is_normal());
    assert!(!SUBNORMAL.is_normal());
    assert!(!(-SUBNORMAL).is_normal());

    ///// is_sign_negative()
    assert!(f32::NEG_INFINITY.is_sign_negative());
    assert!((-0.0f32).is_sign_negative());
    assert!((-SUBNORMAL).is_sign_negative());
    assert!((-NORMAL).is_sign_negative());

    // Per the docs for `is_sign_negative`, the result of calling this function
    // on NAN is not guaranteed to be a particular value.
    // assert!(!f32::NAN.is_sign_negative());
    assert!(!f32::INFINITY.is_sign_negative());
    assert!(!0.0f32.is_sign_negative());
    assert!(!SUBNORMAL.is_sign_negative());
    assert!(!NORMAL.is_sign_negative());

    ///// is_sign_positive()
    assert!(f32::INFINITY.is_sign_positive());
    assert!(0.0f32.is_sign_positive());
    assert!(SUBNORMAL.is_sign_positive());
    assert!(NORMAL.is_sign_positive());

    // Per the docs for `is_sign_negative`, the result of calling this function
    // on NAN is not guaranteed to be a particular value.
    // assert!(!f32::NAN.is_sign_positive());
    assert!(!f32::NEG_INFINITY.is_sign_positive());
    assert!(!(-0.0f32).is_sign_positive());
    assert!(!(-SUBNORMAL).is_sign_positive());
    assert!(!(-NORMAL).is_sign_positive());

    ///// is_subnormal()
    assert!(SUBNORMAL.is_subnormal());
    assert!((-SUBNORMAL).is_subnormal());

    assert!(!f32::NAN.is_subnormal());
    assert!(!f32::INFINITY.is_subnormal());
    assert!(!f32::NEG_INFINITY.is_subnormal());
    assert!(!0.0f32.is_subnormal());
    assert!(!(-0.0f32).is_subnormal());
    assert!(!NORMAL.is_subnormal());
    assert!(!(-NORMAL).is_subnormal());

    ///// next_down()
    assert!(f32::NAN.next_down().is_nan());
    assert_eq!(f32::INFINITY.next_down(), f32::MAX);
    assert_eq!(TINY.next_down(), 0.0f32);
    assert_eq!(0.0f32.next_down(), -TINY);
    assert_eq!((-0.0f32).next_down(), -TINY);
    assert_eq!(f32::MIN.next_down(), f32::NEG_INFINITY);
    assert_eq!(f32::NEG_INFINITY.next_down(), f32::NEG_INFINITY);

    ///// next_up()
    assert!(f32::NAN.next_up().is_nan());
    assert_eq!(f32::NEG_INFINITY.next_up(), f32::MIN);
    assert_eq!((-TINY).next_up(), -0.0f32);
    assert_eq!(0.0f32.next_up(), TINY);
    assert_eq!((-0.0f32).next_up(), TINY);
    assert_eq!(f32::MAX.next_up(), f32::INFINITY);
    assert_eq!(f32::INFINITY.next_up(), f32::INFINITY);

    ///// to_bits()
    assert_eq!(f32::to_bits(12.5f32), 0x41480000);

    ///// total_cmp()

    // NB: We intentionally omit comparisons involving NaNs here, as SMT-LIB
    // does not distinguish different NaN values.

    // negative infinity
    assert_eq!(f32::NEG_INFINITY.total_cmp(&f32::NEG_INFINITY), Ordering::Equal);
    assert_eq!(f32::NEG_INFINITY.total_cmp(&-NORMAL), Ordering::Less);
    assert_eq!(f32::NEG_INFINITY.total_cmp(&-SUBNORMAL), Ordering::Less);
    assert_eq!(f32::NEG_INFINITY.total_cmp(&-0.0f32), Ordering::Less);
    assert_eq!(f32::NEG_INFINITY.total_cmp(&0.0f32), Ordering::Less);
    assert_eq!(f32::NEG_INFINITY.total_cmp(&SUBNORMAL), Ordering::Less);
    assert_eq!(f32::NEG_INFINITY.total_cmp(&NORMAL), Ordering::Less);
    assert_eq!(f32::NEG_INFINITY.total_cmp(&f32::INFINITY), Ordering::Less);

    // negative numbers
    assert_eq!((-NORMAL).total_cmp(&f32::NEG_INFINITY), Ordering::Greater);
    assert_eq!((-NORMAL).total_cmp(&-NORMAL), Ordering::Equal);
    assert_eq!((-NORMAL).total_cmp(&-SUBNORMAL), Ordering::Less);
    assert_eq!((-NORMAL).total_cmp(&-0.0f32), Ordering::Less);
    assert_eq!((-NORMAL).total_cmp(&0.0f32), Ordering::Less);
    assert_eq!((-NORMAL).total_cmp(&SUBNORMAL), Ordering::Less);
    assert_eq!((-NORMAL).total_cmp(&NORMAL), Ordering::Less);
    assert_eq!((-NORMAL).total_cmp(&f32::INFINITY), Ordering::Less);

    // negative subnormal numbers
    assert_eq!((-SUBNORMAL).total_cmp(&f32::NEG_INFINITY), Ordering::Greater);
    assert_eq!((-SUBNORMAL).total_cmp(&-NORMAL), Ordering::Greater);
    assert_eq!((-SUBNORMAL).total_cmp(&-SUBNORMAL), Ordering::Equal);
    assert_eq!((-SUBNORMAL).total_cmp(&-0.0f32), Ordering::Less);
    assert_eq!((-SUBNORMAL).total_cmp(&0.0f32), Ordering::Less);
    assert_eq!((-SUBNORMAL).total_cmp(&SUBNORMAL), Ordering::Less);
    assert_eq!((-SUBNORMAL).total_cmp(&NORMAL), Ordering::Less);
    assert_eq!((-SUBNORMAL).total_cmp(&f32::INFINITY), Ordering::Less);

    // negative zero
    assert_eq!((-0.0f32).total_cmp(&f32::NEG_INFINITY), Ordering::Greater);
    assert_eq!((-0.0f32).total_cmp(&-NORMAL), Ordering::Greater);
    assert_eq!((-0.0f32).total_cmp(&-SUBNORMAL), Ordering::Greater);
    assert_eq!((-0.0f32).total_cmp(&-0.0f32), Ordering::Equal);
    assert_eq!((-0.0f32).total_cmp(&0.0f32), Ordering::Less);
    assert_eq!((-0.0f32).total_cmp(&SUBNORMAL), Ordering::Less);
    assert_eq!((-0.0f32).total_cmp(&NORMAL), Ordering::Less);
    assert_eq!((-0.0f32).total_cmp(&f32::INFINITY), Ordering::Less);

    // positive zero
    assert_eq!(0.0f32.total_cmp(&f32::NEG_INFINITY), Ordering::Greater);
    assert_eq!(0.0f32.total_cmp(&-NORMAL), Ordering::Greater);
    assert_eq!(0.0f32.total_cmp(&-SUBNORMAL), Ordering::Greater);
    assert_eq!(0.0f32.total_cmp(&-0.0f32), Ordering::Greater);
    assert_eq!(0.0f32.total_cmp(&0.0f32), Ordering::Equal);
    assert_eq!(0.0f32.total_cmp(&SUBNORMAL), Ordering::Less);
    assert_eq!(0.0f32.total_cmp(&NORMAL), Ordering::Less);
    assert_eq!(0.0f32.total_cmp(&f32::INFINITY), Ordering::Less);

    // positive subnormal zero
    assert_eq!(SUBNORMAL.total_cmp(&f32::NEG_INFINITY), Ordering::Greater);
    assert_eq!(SUBNORMAL.total_cmp(&-NORMAL), Ordering::Greater);
    assert_eq!(SUBNORMAL.total_cmp(&-SUBNORMAL), Ordering::Greater);
    assert_eq!(SUBNORMAL.total_cmp(&-0.0f32), Ordering::Greater);
    assert_eq!(SUBNORMAL.total_cmp(&0.0f32), Ordering::Greater);
    assert_eq!(SUBNORMAL.total_cmp(&SUBNORMAL), Ordering::Equal);
    assert_eq!(SUBNORMAL.total_cmp(&NORMAL), Ordering::Less);
    assert_eq!(SUBNORMAL.total_cmp(&f32::INFINITY), Ordering::Less);

    // positive numbers
    assert_eq!(NORMAL.total_cmp(&f32::NEG_INFINITY), Ordering::Greater);
    assert_eq!(NORMAL.total_cmp(&-NORMAL), Ordering::Greater);
    assert_eq!(NORMAL.total_cmp(&-SUBNORMAL), Ordering::Greater);
    assert_eq!(NORMAL.total_cmp(&-0.0f32), Ordering::Greater);
    assert_eq!(NORMAL.total_cmp(&0.0f32), Ordering::Greater);
    assert_eq!(NORMAL.total_cmp(&SUBNORMAL), Ordering::Greater);
    assert_eq!(NORMAL.total_cmp(&NORMAL), Ordering::Equal);
    assert_eq!(NORMAL.total_cmp(&f32::INFINITY), Ordering::Less);

    // positive infinity
    assert_eq!(f32::INFINITY.total_cmp(&f32::NEG_INFINITY), Ordering::Greater);
    assert_eq!(f32::INFINITY.total_cmp(&-NORMAL), Ordering::Greater);
    assert_eq!(f32::INFINITY.total_cmp(&-SUBNORMAL), Ordering::Greater);
    assert_eq!(f32::INFINITY.total_cmp(&-0.0f32), Ordering::Greater);
    assert_eq!(f32::INFINITY.total_cmp(&0.0f32), Ordering::Greater);
    assert_eq!(f32::INFINITY.total_cmp(&SUBNORMAL), Ordering::Greater);
    assert_eq!(f32::INFINITY.total_cmp(&NORMAL), Ordering::Greater);
    assert_eq!(f32::INFINITY.total_cmp(&f32::INFINITY), Ordering::Equal);
}

pub fn main() {
    println!("{:?}", crux_test());
}
