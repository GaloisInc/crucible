#![stable(feature = "rust1", since = "1.0.0")]

use crate::fmt;
use crate::marker;

#[stable(feature = "rust1", since = "1.0.0")]
#[allow(deprecated)]
pub use self::sip::SipHasher;

#[unstable(feature = "hashmap_internals", issue = "0")]
#[allow(deprecated)]
#[doc(hidden)]
pub use self::sip::SipHasher13;

mod sip;

/// Every function in this module returns a dummy value, but wraps it in a call to this `dummy_val`
/// function first.  If you want to make functions panic instead of being a no-op, change the
/// implementation here.
fn dummy_val<T>(x: T) -> T {
    x
}

/// Specialized version of `dummy_val` for the many functions that return `fmt::Result`.
fn dummy() {
    dummy_val(())
}

#[stable(feature = "rust1", since = "1.0.0")]
pub trait Hash {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn hash<H: Hasher>(&self, state: &mut H);

    #[stable(feature = "hash_slice", since = "1.3.0")]
    fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)
        where Self: Sized
    {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
pub trait Hasher {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn finish(&self) -> u64;

    #[stable(feature = "rust1", since = "1.0.0")]
    fn write(&mut self, bytes: &[u8]);

    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_u8(&mut self, i: u8) {
        dummy()
    }
    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_u16(&mut self, i: u16) {
        dummy()
    }
    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_u32(&mut self, i: u32) {
        dummy()
    }
    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_u64(&mut self, i: u64) {
        dummy()
    }
    #[inline]
    #[stable(feature = "i128", since = "1.26.0")]
    fn write_u128(&mut self, i: u128) {
        dummy()
    }
    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_usize(&mut self, i: usize) {
        dummy()
    }

    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_i8(&mut self, i: i8) {
        dummy()
    }
    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_i16(&mut self, i: i16) {
        dummy()
    }
    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_i32(&mut self, i: i32) {
        dummy()
    }
    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_i64(&mut self, i: i64) {
        dummy()
    }
    #[inline]
    #[stable(feature = "i128", since = "1.26.0")]
    fn write_i128(&mut self, i: i128) {
        dummy()
    }
    #[inline]
    #[stable(feature = "hasher_write", since = "1.3.0")]
    fn write_isize(&mut self, i: isize) {
        dummy()
    }
}

#[stable(feature = "indirect_hasher_impl", since = "1.22.0")]
impl<H: Hasher + ?Sized> Hasher for &mut H {
    fn finish(&self) -> u64 {
        dummy_val(0)
    }
    fn write(&mut self, bytes: &[u8]) {
        dummy()
    }
    fn write_u8(&mut self, i: u8) {
        dummy()
    }
    fn write_u16(&mut self, i: u16) {
        dummy()
    }
    fn write_u32(&mut self, i: u32) {
        dummy()
    }
    fn write_u64(&mut self, i: u64) {
        dummy()
    }
    fn write_u128(&mut self, i: u128) {
        dummy()
    }
    fn write_usize(&mut self, i: usize) {
        dummy()
    }
    fn write_i8(&mut self, i: i8) {
        dummy()
    }
    fn write_i16(&mut self, i: i16) {
        dummy()
    }
    fn write_i32(&mut self, i: i32) {
        dummy()
    }
    fn write_i64(&mut self, i: i64) {
        dummy()
    }
    fn write_i128(&mut self, i: i128) {
        dummy()
    }
    fn write_isize(&mut self, i: isize) {
        dummy()
    }
}

#[stable(since = "1.7.0", feature = "build_hasher")]
pub trait BuildHasher {
    #[stable(since = "1.7.0", feature = "build_hasher")]
    type Hasher: Hasher;

    #[stable(since = "1.7.0", feature = "build_hasher")]
    fn build_hasher(&self) -> Self::Hasher;
}

#[stable(since = "1.7.0", feature = "build_hasher")]
pub struct BuildHasherDefault<H>(marker::PhantomData<H>);

#[stable(since = "1.9.0", feature = "core_impl_debug")]
impl<H> fmt::Debug for BuildHasherDefault<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        dummy_val(Ok(()))
    }
}

#[stable(since = "1.7.0", feature = "build_hasher")]
impl<H: Default + Hasher> BuildHasher for BuildHasherDefault<H> {
    type Hasher = H;

    fn build_hasher(&self) -> H {
        H::default()
    }
}

#[stable(since = "1.7.0", feature = "build_hasher")]
impl<H> Clone for BuildHasherDefault<H> {
    fn clone(&self) -> BuildHasherDefault<H> {
        BuildHasherDefault(marker::PhantomData)
    }
}

#[stable(since = "1.7.0", feature = "build_hasher")]
impl<H> Default for BuildHasherDefault<H> {
    fn default() -> BuildHasherDefault<H> {
        BuildHasherDefault(marker::PhantomData)
    }
}

#[stable(since = "1.29.0", feature = "build_hasher_eq")]
impl<H> PartialEq for BuildHasherDefault<H> {
    fn eq(&self, _other: &BuildHasherDefault<H>) -> bool {
        true
    }
}

#[stable(since = "1.29.0", feature = "build_hasher_eq")]
impl<H> Eq for BuildHasherDefault<H> {}


mod impls {
    use crate::mem;
    use crate::slice;

    use super::*;

    macro_rules! impl_write {
        ($(($ty:ident, $meth:ident),)*) => {$(
            #[stable(feature = "rust1", since = "1.0.0")]
            impl Hash for $ty {
                fn hash<H: Hasher>(&self, state: &mut H) {
                    dummy()
                }

                fn hash_slice<H: Hasher>(data: &[$ty], state: &mut H) {
                    dummy()
                }
            }
        )*}
    }

    impl_write! {
        (u8, write_u8),
        (u16, write_u16),
        (u32, write_u32),
        (u64, write_u64),
        (usize, write_usize),
        (i8, write_i8),
        (i16, write_i16),
        (i32, write_i32),
        (i64, write_i64),
        (isize, write_isize),
        (u128, write_u128),
        (i128, write_i128),
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl Hash for bool {
        fn hash<H: Hasher>(&self, state: &mut H) {
            dummy()
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl Hash for char {
        fn hash<H: Hasher>(&self, state: &mut H) {
            dummy()
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl Hash for str {
        fn hash<H: Hasher>(&self, state: &mut H) {
            dummy()
        }
    }

    #[stable(feature = "never_hash", since = "1.29.0")]
    impl Hash for ! {
        fn hash<H: Hasher>(&self, _: &mut H) {
            dummy()
        }
    }

    macro_rules! impl_hash_tuple {
        () => (
            #[stable(feature = "rust1", since = "1.0.0")]
            impl Hash for () {
                fn hash<H: Hasher>(&self, _state: &mut H) {}
            }
        );

        ( $($name:ident)+) => (
            #[stable(feature = "rust1", since = "1.0.0")]
            impl<$($name: Hash),+> Hash for ($($name,)+) where last_type!($($name,)+): ?Sized {
                #[allow(non_snake_case)]
                fn hash<S: Hasher>(&self, state: &mut S) {
                    dummy()
                }
            }
        );
    }

    macro_rules! last_type {
        ($a:ident,) => { $a };
        ($a:ident, $($rest_a:ident,)+) => { last_type!($($rest_a,)+) };
    }

    impl_hash_tuple! {}
    impl_hash_tuple! { A }
    impl_hash_tuple! { A B }
    impl_hash_tuple! { A B C }
    impl_hash_tuple! { A B C D }
    impl_hash_tuple! { A B C D E }
    impl_hash_tuple! { A B C D E F }
    impl_hash_tuple! { A B C D E F G }
    impl_hash_tuple! { A B C D E F G H }
    impl_hash_tuple! { A B C D E F G H I }
    impl_hash_tuple! { A B C D E F G H I J }
    impl_hash_tuple! { A B C D E F G H I J K }
    impl_hash_tuple! { A B C D E F G H I J K L }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl<T: Hash> Hash for [T] {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.len().hash(state);
            Hash::hash_slice(self, state)
        }
    }


    #[stable(feature = "rust1", since = "1.0.0")]
    impl<T: ?Sized + Hash> Hash for &T {
        fn hash<H: Hasher>(&self, state: &mut H) {
            (**self).hash(state);
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl<T: ?Sized + Hash> Hash for &mut T {
        fn hash<H: Hasher>(&self, state: &mut H) {
            (**self).hash(state);
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl<T: ?Sized> Hash for *const T {
        fn hash<H: Hasher>(&self, state: &mut H) {
            dummy()
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl<T: ?Sized> Hash for *mut T {
        fn hash<H: Hasher>(&self, state: &mut H) {
            dummy()
        }
    }
}
