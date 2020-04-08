#![cfg_attr(not(with_main), no_std)]
trait FIndex {
    
    type Output : ?Sized;
    
    fn findex(&self, i:usize) -> &Self::Output; 
    
}

impl FIndex for [u8] {
    type Output = u8;
    fn findex(&self, i:usize) -> &u8 {
        &self[i]
    }
}

fn f (x:u8) -> u8 {
    let xs = [x;5];
    *xs.findex(0)
}


const ARG: u8 = 23;


#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> u8 { f(ARG) }
