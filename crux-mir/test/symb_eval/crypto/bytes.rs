#![no_std]

extern crate crucible;
use crucible::*;

// ----------------------------------------------------------------------
pub fn zero() -> [u64;5] {
    [0,0,0,0,0]
}


pub fn from_bytes(bytes: &[u8; 32]) -> [u64; 5] {
    let mut words = [0u64; 4];
    for i in 0..4 {
        for j in 0..8 {
            words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
        }
    }
    
    let mask = (1u64 << 52) - 1;
    let top_mask = (1u64 << 48) - 1;
    let mut s = zero();

    s[ 0] =   words[0]                            & mask;
    s[ 1] = ((words[0] >> 52) | (words[1] << 12)) & mask;
    s[ 2] = ((words[1] >> 40) | (words[2] << 24)) & mask;
    s[ 3] = ((words[2] >> 28) | (words[3] << 36)) & mask;
    s[ 4] =  (words[3] >> 16)                     & top_mask;
    
    s
}

    /// Pack the limbs of this `Scalar64` into 32 bytes
pub fn to_bytes(x :&[u64;5]) -> [u8; 32] {
    let mut s = [0u8; 32];
    
    s[0]  =  (x[ 0] >>  0)                      as u8;
    s[1]  =  (x[ 0] >>  8)                      as u8;
    s[2]  =  (x[ 0] >> 16)                      as u8;
    s[3]  =  (x[ 0] >> 24)                      as u8;
    s[4]  =  (x[ 0] >> 32)                      as u8;
    s[5]  =  (x[ 0] >> 40)                      as u8;
    s[6]  = ((x[ 0] >> 48) | (x[ 1] << 4)) as u8;
    s[7]  =  (x[ 1] >>  4)                      as u8;
    s[8]  =  (x[ 1] >> 12)                      as u8;
    s[9]  =  (x[ 1] >> 20)                      as u8;
    s[10] =  (x[ 1] >> 28)                      as u8;
    s[11] =  (x[ 1] >> 36)                      as u8;
    s[12] =  (x[ 1] >> 44)                      as u8;
    s[13] =  (x[ 2] >>  0)                      as u8;
    s[14] =  (x[ 2] >>  8)                      as u8;
    s[15] =  (x[ 2] >> 16)                      as u8;
    s[16] =  (x[ 2] >> 24)                      as u8;
    s[17] =  (x[ 2] >> 32)                      as u8;
    s[18] =  (x[ 2] >> 40)                      as u8;
    s[19] = ((x[ 2] >> 48) | (x[ 3] << 4)) as u8;
    s[20] =  (x[ 3] >>  4)                      as u8;
    s[21] =  (x[ 3] >> 12)                      as u8;
    s[22] =  (x[ 3] >> 20)                      as u8;
    s[23] =  (x[ 3] >> 28)                      as u8;
    s[24] =  (x[ 3] >> 36)                      as u8;
    s[25] =  (x[ 3] >> 44)                      as u8;
    s[26] =  (x[ 4] >>  0)                      as u8;
    s[27] =  (x[ 4] >>  8)                      as u8;
    s[28] =  (x[ 4] >> 16)                      as u8;
    s[29] =  (x[ 4] >> 24)                      as u8;
    s[30] =  (x[ 4] >> 32)                      as u8;
    s[31] =  (x[ 4] >> 40)                      as u8;
    
    s
}

#[cfg_attr(crux, crux_test)]
pub fn f() {
    let a0 = crucible_u64("a0");
    let a1 = crucible_u64("a1");
    let a2 = crucible_u64("a2");
    let a3 = crucible_u64("a3");
    let a4 = crucible_u64("a4");    
    
    let a = [a0, a1, a2, a3, a4];
    let b = from_bytes(&to_bytes(&a));

    for i in 0..5 {
      crucible_assert!(a[i] == b[i]);
    } 
}
