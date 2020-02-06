use core::ops::{Deref, DerefMut};
use crate::array::Array;

pub struct SymBytes {
    arr: Array<u8>,
    len: usize,
}

impl SymBytes {
    pub fn new(len: usize) -> SymBytes {
        SymBytes {
            arr: Array::zeroed(),
            len,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl Deref for SymBytes {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        self.arr.as_slice(0, self.len)
    }
}

impl DerefMut for SymBytes {
    fn deref_mut(&mut self) -> &mut [u8] {
        self.arr.as_mut_slice(0, self.len)
    }
}
