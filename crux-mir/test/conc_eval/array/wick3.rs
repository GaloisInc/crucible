// FAIL: needs Vec data structure from stdlib
#![cfg_attr(not(with_main), no_std)]

pub fn addn(x: &[u32], y: &[u32]) -> Vec<u32>
 {
     let mut res = Vec::with_capacity(x.len() + 1);
     let mut carry = 0;
 
     assert_eq!(x.len(), y.len());
     for (xval, yval) in x.iter().zip(y.iter()) {
         let val64 = (*xval as u64) + (*yval as u64) + carry;
         res.push(val64 as u32);
         carry = val64 >> 32u64;
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
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> bool { f(ARG) }
