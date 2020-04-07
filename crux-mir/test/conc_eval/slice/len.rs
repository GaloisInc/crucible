#![cfg_attr(not(with_main), no_std)]
fn g(slice:&mut [u16]) -> usize {
    slice.len()
}

fn f(x:u16) -> usize {
    let mut buf = [x;5];
    g(&mut buf)
}


const ARG: u16 = 1;


#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> usize { f(ARG) }
