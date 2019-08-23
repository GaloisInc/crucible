#![cfg_attr(not(with_main), no_std)]
fn f (x : u32) -> u32 {
    
    let mut k = 0;
    loop {
        if k == x {
            break;
        }
        k = k+1;
    }
    return k;
}

const ARG :u32 = 2;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] pub fn main() { f(ARG); }
