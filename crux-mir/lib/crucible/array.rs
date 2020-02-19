use core::marker::PhantomData;
use crate::symbolic::Symbolic;

#[derive(Copy)]
pub struct Array<T>(PhantomData<T>);

// NB: `T: Copy`, not `T: Clone`.  We can't clone all the array elements (like `Vec<T>` does)
// because we don't know which indices are populated.  All we can do is copy the whole array, which
// copies all its elements, and thus is valid only when `T: Copy`.
impl<T: Copy> Clone for Array<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Array<T> {
    /// Construct a new array, filled with zeros.
    ///
    /// While `T` is declared as unconstrained, it's actually required to have a `BaseType`
    /// Crucible representation.  All primitive integer types, as well as the wider bitvectors in
    /// `crucible::bitvector`, satisfy this requirement.
    pub const fn zeroed() -> Array<T> {
        Self::zeroed()
    }
}

impl<T: Copy> Array<T> {
    pub fn lookup(self, idx: usize) -> T {
        unimplemented!("Array::lookup")
    }

    pub fn update(self, idx: usize, x: T) -> Self {
        unimplemented!("Array::update")
    }

    /// Take a slice of this array.  Symbolic arrays have unbounded size, so the caller can request
    /// any offset and bounds they want for the resulting slice.
    pub fn as_slice(&self, start: usize, len: usize) -> &[T] {
        unimplemented!("Array::as_slice")
    }

    pub fn as_mut_slice(&mut self, start: usize, len: usize) -> &mut [T] {
        unimplemented!("Array::as_mut_slice")
    }
}

fn symbolic<T>(desc: &'static str) -> Array<T> {
    unimplemented!("Array::symbolic")
}

impl<T> Symbolic for Array<T> {
    fn symbolic(desc: &'static str) -> Array<T> {
        symbolic(desc)
    }
}

