//! Macros shared throughout the compiler-builtins implementation

/// Changes the visibility to `pub` if feature "public-test-deps" is set
#[cfg(not(feature = "public-test-deps"))]
macro_rules! public_test_dep {
    ($(#[$($meta:meta)*])* pub(crate) $ident:ident $($tokens:tt)*) => {
        $(#[$($meta)*])* pub(crate) $ident $($tokens)*
    };
}

/// Changes the visibility to `pub` if feature "public-test-deps" is set
#[cfg(feature = "public-test-deps")]
macro_rules! public_test_dep {
    {$(#[$($meta:meta)*])* pub(crate) $ident:ident $($tokens:tt)*} => {
        $(#[$($meta)*])* pub $ident $($tokens)*
    };
}

/// The "main macro" used for defining intrinsics.
///
/// The compiler-builtins library is super platform-specific with tons of crazy
/// little tweaks for various platforms. As a result it *could* involve a lot of
/// #[cfg] and macro soup, but the intention is that this macro alleviates a lot
/// of that complexity. Ideally this macro has all the weird ABI things
/// platforms need and elsewhere in this library it just looks like normal Rust
/// code.
///
/// This macro is structured to be invoked with a bunch of functions that looks
/// like:
///
///     intrinsics! {
///         pub extern "C" fn foo(a: i32) -> u32 {
///             // ...
///         }
///
///         #[nonstandard_attribute]
///         pub extern "C" fn bar(a: i32) -> u32 {
///             // ...
///         }
///     }
///
/// Each function is defined in a manner that looks like a normal Rust function.
/// The macro then accepts a few nonstandard attributes that can decorate
/// various functions. Each of the attributes is documented below with what it
/// can do, and each of them slightly tweaks how further expansion happens.
///
/// A quick overview of attributes supported right now are:
///
/// * `maybe_use_optimized_c_shim` - indicates that the Rust implementation is
///   ignored if an optimized C version was compiled.
/// * `aapcs_on_arm` - forces the ABI of the function to be `"aapcs"` on ARM and
///   the specified ABI everywhere else.
/// * `unadjusted_on_win64` - like `aapcs_on_arm` this switches to the
///   `"unadjusted"` abi on Win64 and the specified abi elsewhere.
/// * `win64_128bit_abi_hack` - this attribute is used for 128-bit integer
///   intrinsics where the ABI is slightly tweaked on Windows platforms, but
///   it's a normal ABI elsewhere for returning a 128 bit integer.
/// * `arm_aeabi_alias` - handles the "aliasing" of various intrinsics on ARM
///   their otherwise typical names to other prefixed ones.
///
macro_rules! intrinsics {
    () => ();

    // Support cfg_attr:
    (
        #[cfg_attr($e:meta, $($attr:tt)*)]
        $(#[$($attrs:tt)*])*
        pub extern $abi:tt fn $name:ident( $($argname:ident: $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }
        $($rest:tt)*
    ) => (
        #[cfg($e)]
        intrinsics! {
            #[$($attr)*]
            $(#[$($attrs)*])*
            pub extern $abi fn $name($($argname: $ty),*) $(-> $ret)? {
                $($body)*
            }
        }

        #[cfg(not($e))]
        intrinsics! {
            $(#[$($attrs)*])*
            pub extern $abi fn $name($($argname: $ty),*) $(-> $ret)? {
                $($body)*
            }
        }

        intrinsics!($($rest)*);
    );

    // Right now there's a bunch of architecture-optimized intrinsics in the
    // stock compiler-rt implementation. Not all of these have been ported over
    // to Rust yet so when the `c` feature of this crate is enabled we fall back
    // to the architecture-specific versions which should be more optimized. The
    // purpose of this macro is to easily allow specifying this.
    //
    // The `#[maybe_use_optimized_c_shim]` attribute indicates that this
    // intrinsic may have an optimized C version. In these situations the build
    // script, if the C code is enabled and compiled, will emit a cfg directive
    // to get passed to rustc for our compilation. If that cfg is set we skip
    // the Rust implementation, but if the attribute is not enabled then we
    // compile in the Rust implementation.
    (
        #[maybe_use_optimized_c_shim]
        $(#[$($attr:tt)*])*
        pub extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        #[cfg($name = "optimized-c")]
        pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
            extern $abi {
                fn $name($($argname: $ty),*) $(-> $ret)?;
            }
            unsafe {
                $name($($argname),*)
            }
        }

        #[cfg(not($name = "optimized-c"))]
        intrinsics! {
            $(#[$($attr)*])*
            pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                $($body)*
            }
        }

        intrinsics!($($rest)*);
    );

    // We recognize the `#[aapcs_on_arm]` attribute here and generate the
    // same intrinsic but force it to have the `"aapcs"` calling convention on
    // ARM and `"C"` elsewhere.
    (
        #[aapcs_on_arm]
        $(#[$($attr:tt)*])*
        pub extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        #[cfg(target_arch = "arm")]
        intrinsics! {
            $(#[$($attr)*])*
            pub extern "aapcs" fn $name( $($argname: $ty),* ) $(-> $ret)? {
                $($body)*
            }
        }

        #[cfg(not(target_arch = "arm"))]
        intrinsics! {
            $(#[$($attr)*])*
            pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                $($body)*
            }
        }

        intrinsics!($($rest)*);
    );

    // Like aapcs above we recognize an attribute for the "unadjusted" abi on
    // win64 for some methods.
    (
        #[unadjusted_on_win64]
        $(#[$($attr:tt)*])*
        pub extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        #[cfg(all(any(windows, all(target_os = "uefi", target_arch = "x86_64")), target_pointer_width = "64"))]
        intrinsics! {
            $(#[$($attr)*])*
            pub extern "unadjusted" fn $name( $($argname: $ty),* ) $(-> $ret)? {
                $($body)*
            }
        }

        #[cfg(not(all(any(windows, all(target_os = "uefi", target_arch = "x86_64")), target_pointer_width = "64")))]
        intrinsics! {
            $(#[$($attr)*])*
            pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                $($body)*
            }
        }

        intrinsics!($($rest)*);
    );

    // Some intrinsics on win64 which return a 128-bit integer have an.. unusual
    // calling convention. That's managed here with this "abi hack" which alters
    // the generated symbol's ABI.
    //
    // This will still define a function in this crate with the given name and
    // signature, but the actual symbol for the intrinsic may have a slightly
    // different ABI on win64.
    (
        #[win64_128bit_abi_hack]
        $(#[$($attr:tt)*])*
        pub extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        #[cfg(all(any(windows, target_os = "uefi"), target_arch = "x86_64"))]
        $(#[$($attr)*])*
        pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
            $($body)*
        }

        #[cfg(all(any(windows, target_os = "uefi"), target_arch = "x86_64"))]
        pub mod $name {
            #[cfg_attr(not(feature = "mangled-names"), no_mangle)]
            pub extern $abi fn $name( $($argname: $ty),* )
                -> ::macros::win64_128bit_abi_hack::U64x2
            {
                let e: $($ret)? = super::$name($($argname),*);
                ::macros::win64_128bit_abi_hack::U64x2::from(e)
            }
        }

        #[cfg(not(all(any(windows, target_os = "uefi"), target_arch = "x86_64")))]
        intrinsics! {
            $(#[$($attr)*])*
            pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                $($body)*
            }
        }

        intrinsics!($($rest)*);
    );

    // A bunch of intrinsics on ARM are aliased in the standard compiler-rt
    // build under `__aeabi_*` aliases, and LLVM will call these instead of the
    // original function. The aliasing here is used to generate these symbols in
    // the object file.
    (
        #[arm_aeabi_alias = $alias:ident]
        $(#[$($attr:tt)*])*
        pub extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        #[cfg(target_arch = "arm")]
        pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
            $($body)*
        }

        #[cfg(target_arch = "arm")]
        pub mod $name {
            #[cfg_attr(not(feature = "mangled-names"), no_mangle)]
            pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                super::$name($($argname),*)
            }
        }

        #[cfg(target_arch = "arm")]
        pub mod $alias {
            #[cfg_attr(not(feature = "mangled-names"), no_mangle)]
            #[cfg_attr(all(not(windows), not(target_vendor="apple")), linkage = "weak")]
            pub extern "aapcs" fn $alias( $($argname: $ty),* ) $(-> $ret)? {
                super::$name($($argname),*)
            }
        }

        #[cfg(not(target_arch = "arm"))]
        intrinsics! {
            $(#[$($attr)*])*
            pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                $($body)*
            }
        }

        intrinsics!($($rest)*);
    );

    // C mem* functions are only generated when the "mem" feature is enabled.
    (
        #[mem_builtin]
        $(#[$($attr:tt)*])*
        pub unsafe extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        $(#[$($attr)*])*
        pub unsafe extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
            $($body)*
        }

        #[cfg(feature = "mem")]
        pub mod $name {
            $(#[$($attr)*])*
            #[cfg_attr(not(feature = "mangled-names"), no_mangle)]
            pub unsafe extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                super::$name($($argname),*)
            }
        }

        intrinsics!($($rest)*);
    );

    // Naked functions are special: we can't generate wrappers for them since
    // they use a custom calling convention.
    (
        #[naked]
        $(#[$($attr:tt)*])*
        pub unsafe extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        pub mod $name {
            #[naked]
            $(#[$($attr)*])*
            #[cfg_attr(not(feature = "mangled-names"), no_mangle)]
            pub unsafe extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                $($body)*
            }
        }

        intrinsics!($($rest)*);
    );

    // For division and modulo, AVR uses a custom calling convention¹ that does
    // not match our definitions here. Ideally we would just use hand-written
    // naked functions, but that's quite a lot of code to port² - so for the
    // time being we are just ignoring the problematic functions, letting
    // avr-gcc (which is required to compile to AVR anyway) link them from
    // libgcc.
    //
    // ¹ https://gcc.gnu.org/wiki/avr-gcc (see "Exceptions to the Calling
    //   Convention")
    // ² https://github.com/gcc-mirror/gcc/blob/31048012db98f5ec9c2ba537bfd850374bdd771f/libgcc/config/avr/lib1funcs.S
    (
        #[avr_skip]
        $(#[$($attr:tt)*])*
        pub extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        #[cfg(not(target_arch = "avr"))]
        intrinsics! {
            $(#[$($attr)*])*
            pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                $($body)*
            }
        }

        intrinsics!($($rest)*);
    );

    // This is the final catch-all rule. At this point we generate an
    // intrinsic with a conditional `#[no_mangle]` directive to avoid
    // interfering with duplicate symbols and whatnot during testing.
    //
    // The implementation is placed in a separate module, to take advantage
    // of the fact that rustc partitions functions into code generation
    // units based on module they are defined in. As a result we will have
    // a separate object file for each intrinsic. For further details see
    // corresponding PR in rustc https://github.com/rust-lang/rust/pull/70846
    //
    // After the intrinsic is defined we just continue with the rest of the
    // input we were given.
    (
        $(#[$($attr:tt)*])*
        pub extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        $(#[$($attr)*])*
        pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
            $($body)*
        }

        pub mod $name {
            $(#[$($attr)*])*
            #[cfg_attr(not(feature = "mangled-names"), no_mangle)]
            pub extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                super::$name($($argname),*)
            }
        }

        intrinsics!($($rest)*);
    );

    // Same as the above for unsafe functions.
    (
        $(#[$($attr:tt)*])*
        pub unsafe extern $abi:tt fn $name:ident( $($argname:ident:  $ty:ty),* ) $(-> $ret:ty)? {
            $($body:tt)*
        }

        $($rest:tt)*
    ) => (
        $(#[$($attr)*])*
        pub unsafe extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
            $($body)*
        }

        pub mod $name {
            $(#[$($attr)*])*
            #[cfg_attr(not(feature = "mangled-names"), no_mangle)]
            pub unsafe extern $abi fn $name( $($argname: $ty),* ) $(-> $ret)? {
                super::$name($($argname),*)
            }
        }

        intrinsics!($($rest)*);
    );
}

// Hack for LLVM expectations for ABI on windows. This is used by the
// `#[win64_128bit_abi_hack]` attribute recognized above
#[cfg(all(any(windows, target_os = "uefi"), target_pointer_width = "64"))]
pub mod win64_128bit_abi_hack {
    #[repr(simd)]
    pub struct U64x2(u64, u64);

    impl From<i128> for U64x2 {
        fn from(i: i128) -> U64x2 {
            use int::DInt;
            let j = i as u128;
            U64x2(j.lo(), j.hi())
        }
    }

    impl From<u128> for U64x2 {
        fn from(i: u128) -> U64x2 {
            use int::DInt;
            U64x2(i.lo(), i.hi())
        }
    }
}
