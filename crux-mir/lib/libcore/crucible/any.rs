//! Defines bindings to Crucible's `AnyType`.

/// Dynamically-typed wrapper, corresponding to Crucible's `AnyType`.
#[unstable(feature = "crucible_intrinsics", issue = "none")]
#[derive(Clone, Copy, Debug)]
pub struct Any(());

impl Any {
    /// Wrap an arbitrary value in `Any`.
    #[unstable(feature = "crucible_intrinsics", issue = "none")]
    pub fn new<T: Copy>(_x: T) -> Any {
        unimplemented!("Any::new")
    }

    /// Try to downcast to concrete type `T`.  This succeeds if the type passed to `new` has the
    /// same Crucible representation as the type passed to `downcast` (similar to the condition on
    /// `crucible_identity_transmute`).  There is not actually any way to check for an exact type
    /// match at the Rust level.
    ///
    /// This function is unsafe because `new` + `downcast` is equivalent to
    /// `crucible_identity_transmute`.
    #[unstable(feature = "crucible_intrinsics", issue = "none")]
    pub unsafe fn downcast<T>(self) -> T {
        unimplemented!("Any::downcast")
    }
}

