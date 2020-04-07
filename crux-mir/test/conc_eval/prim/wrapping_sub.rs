#![cfg_attr(not(with_main), no_std)]
fn f(_x : u16) -> bool {
    let y : u16 = 20;
    let z : i16 = 20;
    
    let mut res : bool = true;
    
    res = res && y.wrapping_sub(22) == 65534;
    res = res && y.wrapping_sub(18) == 2;
    res = res && z.wrapping_sub(22) == 65534_u16 as i16;
    res = res && z.wrapping_sub(18) == 2;

    res
}

const ARG : u16 = 20;

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> bool { f(ARG) }
