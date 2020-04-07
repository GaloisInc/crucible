#![cfg_attr(not(with_main), no_std)]



fn add3(x: [u32; 3], y: [u32; 3]) -> [u32;4]
{
    let mut output = [0; 4];

    let big0: u64 = (x[0] as u64) + (y[0] as u64);
    let carry0: u64 = big0 >> 32u64;
    let big1: u64 = (x[1] as u64) + (y[1] as u64) + carry0;
    let carry1: u64 = big1 >> 32u64;
    let big2: u64 = (x[2] as u64) + (y[2] as u64) + carry1;
    let carry2: u64 = big2 >> 32u64;
    let big3: u64 = carry2;

    output[0] = big0 as u32;
    output[1] = big1 as u32;
    output[2] = big2 as u32;
    output[3] = big3 as u32;

    output
}

fn f(m: u32) -> bool {
    let x = [m,m,m];
    let y = [2,3,4];

    let z = add3(x,y);

    z[0] == 2+m
}

const ARG:u32 = 4;



#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> bool { f(ARG) }
