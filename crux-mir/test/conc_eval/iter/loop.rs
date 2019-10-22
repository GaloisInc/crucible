#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]
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
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
