
#[macro_use] extern crate crucible;

#[cfg_attr(crux, crux_test)]
pub fn f() {
    let mut v = vec![1_i32, 3, 2];
    v.sort_by_key(|&x| -x);
    crucible_assert!(&v as &[_] == &[3, 2, 1]);
}
