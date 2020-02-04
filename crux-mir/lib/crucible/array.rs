use core::marker::PhantomData;

#[derive(Copy)]
pub struct Array<T>(PhantomData<T>);

// NB: `T: Copy`, not `T: Clone`.  Using `clone` would require us to know all populated indices of
// the array, which we don't.
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

