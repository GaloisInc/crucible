pub trait Symbolic: Sized {
    /// Create a new symbolic value of this type.  `desc` is used to refer to this symbolic value
    /// when printing counterexamples.
    fn symbolic(desc: &'static str) -> Self;

    /// Create a new symbolic value, subject to constraints.  The result is a symbolic value of
    /// this type on which `f` returns `true`.
    fn symbolic_where<F: FnOnce(&Self) -> bool>(desc: &'static str, f: F) -> Self {
        let x = Self::symbolic(desc);
        super::crucible_assume!(f(&x));
        x
    }
}


macro_rules! uint_impls {
    ($($ty:ty, $func:ident;)*) => {
        $(
            /// Hook for a crucible override that creates a symbolic instance of $ty.
            #[allow(unused)]
            fn $func(desc: &'static str) -> $ty { unimplemented!(stringify!($func)); }

            impl Symbolic for $ty {
                fn symbolic(desc: &'static str) -> $ty { $func(desc) }
            }
        )*
    };
}

uint_impls! {
    u8, symbolic_u8;
    u16, symbolic_u16;
    u32, symbolic_u32;
    u64, symbolic_u64;
    u128, symbolic_u128;
}


macro_rules! usize_impls {
    ($($ty:ty, $width:expr;)*) => {
        $(
            #[cfg(target_pointer_width = $width)]
            impl Symbolic for usize {
                fn symbolic(desc: &'static str) -> usize { <$ty>::symbolic(desc) as usize }
            }
        )*
    };
}

usize_impls! {
    u8, "8";
    u16, "16";
    u32, "32";
    u64, "64";
    u128, "128";
}


macro_rules! int_impls {
    ($($ty:ty, $uty:ty;)*) => {
        $(
            impl Symbolic for $ty {
                fn symbolic(desc: &'static str) -> $ty { <$uty>::symbolic(desc) as $ty }
            }
        )*
    };
}

int_impls! {
    i8, u8;
    i16, u16;
    i32, u32;
    i64, u64;
    i128, u128;
    isize, usize;
}

impl Symbolic for bool {
    fn symbolic(desc: &'static str) -> bool {
        let val = u8::symbolic_where(desc, |&x| x < 2);
        val == 1
    }
}


macro_rules! array_impls {
    ($($size:expr)*) => {
        $(
            impl<T: Symbolic + Copy> Symbolic for [T; $size] {
                fn symbolic(desc: &'static str) -> [T; $size] {
                    let mut arr = [T::symbolic(desc); $size];
                    for i in 1 .. $size {
                        arr[i] = T::symbolic(desc);
                    }
                    arr
                }
            }
        )*
    };
}

array_impls! {
    0 1 2 3 4 5 6 7 8 9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32
}

macro_rules! tuple_impls {
    ($($($name:ident)*;)*) => {
        $(
            #[allow(unused)] #[allow(bad_style)]
            impl<$($name: Symbolic,)*> Symbolic for ($($name,)*) {
                fn symbolic(desc: &'static str) -> ($($name,)*) {
                    (
                        $($name::symbolic(desc),)*
                    )
                }
            }
        )*
    };
}

tuple_impls! {
    ;
    A;
    A B;
    A B C;
    A B C D;
    A B C D E;
    A B C D E F;
    A B C D E F G;
    A B C D E F G H;
    A B C D E F G H I;
    A B C D E F G H I J;
    A B C D E F G H I J K;
    A B C D E F G H I J K L;
}


/// Take a symbolic-length prefix of `xs`.  The length of the returned slice can be anywhere in the
/// range `0 ..= xs.len()`.
pub fn prefix<'a, T>(xs: &'a [T]) -> &'a [T] {
    let len = usize::symbolic_where("prefix_len", |&n| n < xs.len());
    &xs[..len]
}
