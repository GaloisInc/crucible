use std::iter;

#[cfg_attr(crux, crux_test)]
pub fn f() {
    let mut i = 0;
    let sum: i32 = iter::from_fn(|| {
        i += 1;
        if i < 5 { Some(i) } else { None }
    }).sum();
    assert!(sum == 10);
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
