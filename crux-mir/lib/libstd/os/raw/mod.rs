//! Platform-specific types, as defined by C.
//!
//! Code that interacts via FFI will almost certainly be using the
//! base types provided by C, which aren't nearly as nicely defined
//! as Rust's primitive types. This module provides types which will
//! match those defined by C, so that code that interacts with C will
//! refer to the correct types.

#![stable(feature = "raw_os", since = "1.1.0")]

#[doc(include = "char.md")]
#[cfg(any(
    all(
        target_os = "linux",
        any(
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "hexagon",
            target_arch = "powerpc",
            target_arch = "powerpc64",
            target_arch = "s390x",
            target_arch = "riscv64"
        )
    ),
    all(target_os = "android", any(target_arch = "aarch64", target_arch = "arm")),
    all(target_os = "l4re", target_arch = "x86_64"),
    all(
        target_os = "freebsd",
        any(
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "powerpc",
            target_arch = "powerpc64"
        )
    ),
    all(
        target_os = "netbsd",
        any(target_arch = "aarch64", target_arch = "arm", target_arch = "powerpc")
    ),
    all(target_os = "openbsd", target_arch = "aarch64"),
    all(
        target_os = "vxworks",
        any(
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "powerpc64",
            target_arch = "powerpc"
        )
    ),
    all(target_os = "fuchsia", target_arch = "aarch64")
))]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_char = u8;
#[doc(include = "char.md")]
#[cfg(not(any(
    all(
        target_os = "linux",
        any(
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "hexagon",
            target_arch = "powerpc",
            target_arch = "powerpc64",
            target_arch = "s390x",
            target_arch = "riscv64"
        )
    ),
    all(target_os = "android", any(target_arch = "aarch64", target_arch = "arm")),
    all(target_os = "l4re", target_arch = "x86_64"),
    all(
        target_os = "freebsd",
        any(
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "powerpc",
            target_arch = "powerpc64"
        )
    ),
    all(
        target_os = "netbsd",
        any(target_arch = "aarch64", target_arch = "arm", target_arch = "powerpc")
    ),
    all(target_os = "openbsd", target_arch = "aarch64"),
    all(
        target_os = "vxworks",
        any(
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "powerpc64",
            target_arch = "powerpc"
        )
    ),
    all(target_os = "fuchsia", target_arch = "aarch64")
)))]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_char = i8;
#[doc(include = "schar.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_schar = i8;
#[doc(include = "uchar.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_uchar = u8;
#[doc(include = "short.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_short = i16;
#[doc(include = "ushort.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_ushort = u16;
#[doc(include = "int.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_int = i32;
#[doc(include = "uint.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_uint = u32;
#[doc(include = "long.md")]
#[cfg(any(target_pointer_width = "32", windows))]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_long = i32;
#[doc(include = "ulong.md")]
#[cfg(any(target_pointer_width = "32", windows))]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_ulong = u32;
#[doc(include = "long.md")]
#[cfg(all(target_pointer_width = "64", not(windows)))]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_long = i64;
#[doc(include = "ulong.md")]
#[cfg(all(target_pointer_width = "64", not(windows)))]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_ulong = u64;
#[doc(include = "longlong.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_longlong = i64;
#[doc(include = "ulonglong.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_ulonglong = u64;
#[doc(include = "float.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_float = f32;
#[doc(include = "double.md")]
#[stable(feature = "raw_os", since = "1.1.0")]
pub type c_double = f64;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(no_inline)]
pub use core::ffi::c_void;

#[cfg(test)]
#[allow(unused_imports)]
mod tests {
    use crate::any::TypeId;
    use crate::mem;

    macro_rules! ok {
        ($($t:ident)*) => {$(
            assert!(TypeId::of::<libc::$t>() == TypeId::of::<raw::$t>(),
                    "{} is wrong", stringify!($t));
        )*}
    }

    #[test]
    fn same() {
        use crate::os::raw;
        ok!(c_char c_schar c_uchar c_short c_ushort c_int c_uint c_long c_ulong
            c_longlong c_ulonglong c_float c_double);
    }
}
