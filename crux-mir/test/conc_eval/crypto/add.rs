// Remove the Scalar64 ADT


mod constants {
    /// `L` is the order of base point, i.e. 2^252 + 27742317777372353535851937790883648493
    pub(crate) const L: [u64;5] = [ 0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0x0000000000000000, 0x0000100000000000 ];
}


pub fn zero() -> [u64;5] {
    [0,0,0,0,0]
}

pub fn add(a: &[u64;5], b: &[u64;5]) -> [u64;5] {
    let mut sum = zero();
    let mask = (1u64 << 52) - 1;
    
    // a + b
    let mut carry: u64 = 0;
    for i in 0..5 {
        carry = a[i] + b[i] + (carry >> 52);
        sum[i] = carry & mask;
    }
    
    // subtract l if the sum is >= l
    sub(&sum, &constants::L)
}

/// Compute `a - b` (mod l)
pub fn sub(a: &[u64;5], b: &[u64;5]) -> [u64;5] {
    let mut difference = zero();
    let mask = (1u64 << 52) - 1;

    // a - b
    let mut borrow: u64 = 0;
    for i in 0..5 {
        borrow = a[i].wrapping_sub(b[i] + (borrow >> 63));
        difference[i] = borrow & mask;
    }

    // conditionally add l if the difference is negative
    let underflow_mask = ((borrow >> 63) ^ 1).wrapping_sub(1);
    let mut carry: u64 = 0;
    for i in 0..5 {
        carry = (carry >> 52) + difference[i] + (constants::L[i] & underflow_mask);
        difference[i] = carry & mask;
    }

    difference
}


const ARG: u64 = 20;

fn f(_w : u64 ) -> bool {
    // a = 2351415481556538453565687241199399922945659411799870114962672658845158063753
    let a =
        [0x0005236c07b3be89, 0x0001bc3d2a67c0c4, 0x000a4aa782aae3ee, 0x0006b3f6e4fec4c4,
         0x00000532da9fab8c];

    // b = 4885590095775723760407499321843594317911456947580037491039278279440296187236
    let b = 
        [0x000d3fae55421564, 0x000c2df24f65a4bc, 0x0005b5587d69fb0b, 0x00094c091b013b3b,
         0x00000acd25605473];

    let res = add(&a, &b);
    let zero = zero();
    let mut ans = true;
    for i in 0..5 {
        // Cannot do assert! yet
        ans = ans && (res[i] == zero[i]);
    }
    ans
}


#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
