//! Crucible pointer intrinsics used within libcore.

/// Pointer-to-usize comparison.  Unlike `ptr as usize == val`, this works on fat pointers and
/// valid pointers too (pointers not created via integer-to-pointer casts).
#[unstable(feature = "crucible_intrinsics", issue = "none")]
pub fn compare_usize<T: ?Sized>(ptr: *const T, val: usize) -> bool {
    unimplemented!("ptr::compare_usize")
}
