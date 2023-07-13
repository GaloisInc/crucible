#![no_std]
extern crate crucible;
use crucible::*;

// ----------------------------------------------------------------------
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

fn ffs_imp(j : u32) -> u32 {
    let mut i = j;
    let mut n : u8 = 1;
    if (i & 0xffff) == 0 { n += 16; i >>= 16; }
    if (i & 0x00ff) == 0 { n +=  8; i >>=  8; }
    if (i & 0x000f) == 0 { n +=  4; i >>=  4; }
    if (i & 0x0003) == 0 { n +=  2; i >>=  2; }
    let nn = n as u32;
    if i != 0 { return nn+((i.wrapping_add(1)) & 0x01); } else { return 0; }
}


#[crux::test]
pub fn f () {
    let a0 = crucible_u32("a0");
    crucible_assert!(ffs_ref(a0) == ffs_imp(a0));
}
