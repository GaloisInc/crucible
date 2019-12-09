//! The first version of the prelude of The Rust Standard Library.
//!
//! See the [module-level documentation](../index.html) for more.



#![stable(feature = "rust1", since = "1.0.0")]

// Re-exported core operators
#[cfg(bootstrap)]
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::marker::Copy;
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::marker::{Send, Sized, Sync, Unpin};
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::ops::{Drop, Fn, FnMut, FnOnce};

// Re-exported functions
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::mem::drop;

// Re-exported types and traits
#[cfg(bootstrap)]
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::clone::Clone;
#[cfg(bootstrap)]
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::cmp::{PartialEq, PartialOrd, Eq, Ord};
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::convert::{AsRef, AsMut, Into, From};
#[cfg(bootstrap)]
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::default::Default;
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::iter::{Iterator, Extend, IntoIterator};
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::iter::{DoubleEndedIterator, ExactSizeIterator};
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::option::Option::{self, Some, None};
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::result::Result::{self, Ok, Err};

// Re-exported built-in macros
#[cfg(not(bootstrap))]
#[stable(feature = "builtin_macro_prelude", since = "1.38.0")]
#[doc(no_inline)]
pub use core::prelude::v1::{
    __rust_unstable_column,
    asm,
    assert,
    cfg,
    column,
    compile_error,
    concat,
    concat_idents,
    env,
    file,
    format_args,
    format_args_nl,
    global_asm,
    include,
    include_bytes,
    include_str,
    line,
    log_syntax,
    module_path,
    option_env,
    stringify,
    trace_macros,
};

// FIXME: Attribute and derive macros are not documented because for them rustdoc generates
// dead links which fail link checker testing.
#[cfg(not(bootstrap))]
#[stable(feature = "builtin_macro_prelude", since = "1.38.0")]
#[allow(deprecated)]
#[doc(hidden)]
pub use core::prelude::v1::{
    Clone,
    Copy,
    Debug,
    Default,
    Eq,
    Hash,
    Ord,
    PartialEq,
    PartialOrd,
    RustcDecodable,
    RustcEncodable,
    bench,
    global_allocator,
    test,
    test_case,
};

// The file so far is equivalent to src/libcore/prelude/v1.rs,
// and below to src/liballoc/prelude.rs.
// Those files are duplicated rather than using glob imports
// because we want docs to show these re-exports as pointing to within `std`.


#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::boxed::Box;
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::borrow::ToOwned;
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::string::{String, ToString};
#[stable(feature = "rust1", since = "1.0.0")]
#[doc(no_inline)]
pub use crate::vec::Vec;
