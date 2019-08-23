#![cfg_attr(not(with_main), no_std)]
// FAIL: needs Vec data structure from stdlib
// https://github.com/rust-lang/rust/blob/master/src/liballoc/vec.rs

pub fn addn(x: &[u32], y: &[u32]) -> Vec<u32>
{
    let mut res = Vec::with_capacity(x.len() + 1);
    let mut carry = 0;
    let mut i = 0;

    assert_eq!(x.len(), y.len());
    while i < x.len() {
        let val64 = (x[i] as u64) + (y[i] as u64) + carry;
        res.push(val64 as u32);
        carry = val64 >> 32u64;
        i += 1;
    }
    res.push(carry as u32);

    res
}


fn f(m: u32) -> bool {
    let x = [m,m,m];
    let y = [2,3,4];

    let z = addn(&x,&y);

    z[0] == 2+m
}

const ARG:u32 = 4;



#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] pub fn main() { f(ARG); }
