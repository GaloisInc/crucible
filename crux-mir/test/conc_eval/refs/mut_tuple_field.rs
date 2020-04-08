#![cfg_attr(not(with_main), no_std)]

#[cfg_attr(crux, crux_test)]
pub fn f() {
    let mut xy = (1, 2);
    let x = &mut xy.0;
    let y = &mut xy.1;
    *x = 3;
    *y = 4;
    assert!(xy == (3, 4));
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
