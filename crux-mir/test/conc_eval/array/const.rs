#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]
mod constants {
    pub(crate) const L: [u64;1] = [ 1 ];
}



const ARG: u64 = 20;

fn f(_w : u64 ) -> u64 {
    constants::L[0] 
}


#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u64 { f(ARG) }
