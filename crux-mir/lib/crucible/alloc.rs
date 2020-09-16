/// Allocate an array of `len` elements of type `T`.  The array begins uninitialized.
pub fn allocate<T>(len: usize) -> *mut T {
    unimplemented!("allocate")
}

/// Allocate an array of `len` elements of type `T`.  The array initially contains all zeros.  This
/// fails if `mir-verifier` doesn't know how to zero-initialize `T`.
pub fn allocate_zeroed<T>(len: usize) -> *mut T {
    unimplemented!("allocate_zeroed")
}

/// Reallocate the array at `*ptr` to contain `new_len` elements.  This reallocation always happens
/// in-place and never fails, so there is no need to return a new pointer.
pub fn reallocate<T>(ptr: *mut T, new_len: usize) {
    unimplemented!("reallocate")
}
