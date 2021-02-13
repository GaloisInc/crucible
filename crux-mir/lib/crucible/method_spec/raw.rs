/// Crucible `MethodSpecType`, exposed to Rust.
///
/// As usual for Crucible types, this implements `Copy`, since it's backed by a boxed,
/// garbage-collected Haskell value.  It contains a dummy field to ensure the Rust compiler sees it
/// as having non-zero size.  The representation is overridden within `crux-mir`, so the field
/// should not be accessed when running symbolically.
#[derive(Clone, Copy)]
pub struct MethodSpec(u8);

// We only have `libcore` available, so we can't return `String` here.  Instead, the override for
// this function within `crux-mir` will construct and leak a `str`.
pub fn spec_pretty_print(ms: MethodSpec) -> &'static str {
    "(unknown MethodSpec)"
}

/// Enable using `ms` in place of calls to the actual function.  The function to override is
/// determined by the `F` type parameter of `builder_new` during the construction of the
/// `MethodSpec`.
pub fn spec_enable(ms: MethodSpec) {
}


/// Crucible `MethodSpecBuilderType`, exposed to Rust.
#[derive(Clone, Copy)]
pub struct MethodSpecBuilder(u8);

pub fn builder_new<F>() -> MethodSpecBuilder {
    // If the program is running under ordinary `crux-mir` instead of `crux-mir-comp`, then the
    // override for this function will be missing.  We could provide a dummy implementation for
    // that case, but it's better to fail early.  Otherwise users will get cryptic errors when
    // invoking their spec functions, as `builder_finish` won't have its usual effect of discarding
    // any new goals added by the spec function.
    unimplemented!("MethodSpecBuilder is not supported on this version of crux-mir")
}

pub fn builder_add_arg<T>(msb: MethodSpecBuilder, x: &T) -> MethodSpecBuilder {
    let _ = x;
    msb
}

pub fn builder_gather_assumes(msb: MethodSpecBuilder) -> MethodSpecBuilder {
    msb
}

pub fn builder_set_return<T>(msb: MethodSpecBuilder, x: &T) -> MethodSpecBuilder {
    let _ = x;
    msb
}

pub fn builder_gather_asserts(msb: MethodSpecBuilder) -> MethodSpecBuilder {
    msb
}

pub fn builder_finish(msb: MethodSpecBuilder) -> MethodSpec {
    let _ = msb;
    MethodSpec(0)
}
