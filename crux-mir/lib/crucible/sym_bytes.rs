use core::ops::{Deref, DerefMut};
use crate::crucible_assume;
use crate::array::Array;
use crate::symbolic::Symbolic;

pub struct SymBytes {
    arr: Array<u8>,
    len: usize,
}

impl SymBytes {
    /// Create a new byte array, filling slots `0 .. len` with zeros.
    pub fn zeroed(len: usize) -> SymBytes {
        SymBytes {
            arr: Array::zeroed(),
            len,
        }
    }

    /// Create a new byte array, filling slots `0 .. len` with symbolic values.
    ///
    /// This is like the trait method `Symbolic::symbolic`, but takes an additional `len` argument.
    pub fn symbolic(desc: &'static str, len: usize) -> SymBytes {
        SymBytes {
            arr: Array::symbolic(desc),
            len,
        }
    }

    /// Create a new byte array, filling slots `0 .. len` with symbolic values, and constraining
    /// the result with `f`.
    ///
    /// This is like the trait method `Symbolic::symbolic`, but takes an additional `len` argument.
    pub fn symbolic_where<F>(desc: &'static str, len: usize, f: F) -> SymBytes
    where F: FnOnce(&Self) -> bool {
        let s = Self::symbolic(desc, len);
        crucible_assume!(f(&s));
        s
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
