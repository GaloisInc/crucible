pub struct Any(());

impl Any {
    /// Wrap an arbitrary value in `Any`.
    pub fn new<T>(x: T) -> Any {
        unimplemented!()
    }

    /// Try to downcast to concrete type `T`.  This succeeds if the type passed to `new` has the
    /// same Crucible representation as the type passed to `downcast` (similar to the condition on
    /// `crucible_identity_transmute`).  There is not actually any way to check for an exact type
    /// match at the Rust level.
    ///
    /// This function is unsafe because `new` + `downcast` is equivalent to
    /// `crucible_identity_transmute`.
    pub unsafe fn downcast<T>(self) -> T {
        unimplemented!()
    }
}
