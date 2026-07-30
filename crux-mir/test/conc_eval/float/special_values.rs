#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    let pos_inf = f32::INFINITY;
    assert_eq!(pos_inf, pos_inf);
    assert!(0.0 < pos_inf);
    assert!(pos_inf.is_infinite());
    assert!(!pos_inf.is_nan());

    let neg_inf = f32::NEG_INFINITY;
    assert_eq!(neg_inf, neg_inf);
    assert!(neg_inf < 0.0);
    assert!(neg_inf.is_infinite());
    assert!(!neg_inf.is_nan());

    let nan = f32::NAN;
    assert!(nan != nan);
    assert!(!(nan <  nan));
    assert!(!(nan <= nan));
    assert!(!(nan >  nan));
    assert!(!(nan >= nan));
    assert!(!nan.is_infinite());
    assert!(nan.is_nan());

    let pos_zero = 0.0f32;
    let neg_zero = -0.0f32;
    assert_eq!(pos_zero, neg_zero);
    assert!(!(pos_zero < neg_zero));
    assert!(pos_zero <= neg_zero);
    assert!(!(pos_zero > neg_zero));
    assert!(pos_zero >= neg_zero);
}

pub fn main() {
    println!("{:?}", crux_test());
}
