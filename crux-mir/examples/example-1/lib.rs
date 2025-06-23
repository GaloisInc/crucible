#[cfg(crux)] extern crate crucible;
#[cfg(crux)] use crucible::*;

/// Find-first-set (fast implementation)
pub fn ffs_fast(mut i: u32) -> u32 {
    let mut n = 1;
    if (i & 0xffff) == 0 { n += 16; i >>= 16; }
    if (i & 0x00ff) == 0 { n +=  8; i >>=  8; }
    if (i & 0x000f) == 0 { n +=  4; i >>=  4; }
    if (i & 0x0003) == 0 { n +=  2; i >>=  2; }
    if i != 0 {
        return n + ((i.wrapping_add(1)) & 0x01);
    } else {
        return 0;
    }
}

/// Find-first-set (reference implementation)
pub fn ffs_ref(word: u32) -> u32 {
    for i in 0 .. 32 {
        if word & (1 << i) != 0 {
            return i + 1;
        }
    }
    return 0;
}

/// Check that ffs_fast and ffs_ref produce the same output on a single input.
#[test]
fn test_ffs_correct_concrete() {
    let x = 12345;
    let a = ffs_ref(x);
    let b = ffs_fast(x);
    assert!(a == b);
}

/// Check that ffs_fast and ffs_ref produce the same output on *every* input.
#[cfg_attr(crux, crux::test)]
fn test_ffs_correct() {
    let x = u32::symbolic("x");
    let a = ffs_ref(x);
    let b = ffs_fast(x);
    assert!(a == b);
}
