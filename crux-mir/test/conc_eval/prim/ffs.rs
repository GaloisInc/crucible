#![cfg_attr(not(with_main), no_std)]

fn ffs_ref(word : u32) -> u32 {
    let mut i : u32 = 0;
    if word == 0 {
        return 0;
    }
    for _cnt in 0 .. 32 {
        if ((1 << i) & word) != 0
        { return i+1; }
        i = i+1;
    }
    return 0;
}

fn ffs_imp(mut i : u32) -> u32 {
    let mut n : u8 = 1;
    if (i & 0xffff) == 0 { n += 16; i >>= 16; }
    if (i & 0x00ff) == 0 { n +=  8; i >>=  8; }
    if (i & 0x000f) == 0 { n +=  4; i >>=  4; }
    if (i & 0x0003) == 0 { n +=  2; i >>=  2; }
    let nn = n as u32;
    if i != 0 { return nn+((i+1) & 0x01); } else { return 0; }
}


fn f (arg : u32) -> bool {
   return ffs_ref(arg) == ffs_imp (arg);
}

const ARG: u32 = 28;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> bool { f(ARG) }
