#![allow(deprecated)] // the types in this module are deprecated

use super::{dummy, dummy_val};

#[unstable(feature = "hashmap_internals", issue = "0")]
#[rustc_deprecated(since = "1.13.0",
                   reason = "use `std::collections::hash_map::DefaultHasher` instead")]
#[derive(Debug, Clone, Default)]
#[doc(hidden)]
pub struct SipHasher13 {
}

#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_deprecated(since = "1.13.0",
                   reason = "use `std::collections::hash_map::DefaultHasher` instead")]
#[derive(Debug, Clone, Default)]
pub struct SipHasher {
}

impl SipHasher {
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_deprecated(since = "1.13.0",
                       reason = "use `std::collections::hash_map::DefaultHasher` instead")]
    pub fn new() -> SipHasher {
        SipHasher { }
    }

    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_deprecated(since = "1.13.0",
                       reason = "use `std::collections::hash_map::DefaultHasher` instead")]
    pub fn new_with_keys(key0: u64, key1: u64) -> SipHasher {
        SipHasher { }
    }
}

impl SipHasher13 {
    #[inline]
    #[unstable(feature = "hashmap_internals", issue = "0")]
    #[rustc_deprecated(since = "1.13.0",
                       reason = "use `std::collections::hash_map::DefaultHasher` instead")]
    pub fn new() -> SipHasher13 {
        SipHasher13 { }
    }

    #[inline]
    #[unstable(feature = "hashmap_internals", issue = "0")]
    #[rustc_deprecated(since = "1.13.0",
                       reason = "use `std::collections::hash_map::DefaultHasher` instead")]
    pub fn new_with_keys(key0: u64, key1: u64) -> SipHasher13 {
        SipHasher13 { }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl super::Hasher for SipHasher {
    #[inline]
    fn write(&mut self, msg: &[u8]) {
        dummy()
    }

    #[inline]
    fn finish(&self) -> u64 {
        dummy_val(0)
    }
}

#[unstable(feature = "hashmap_internals", issue = "0")]
impl super::Hasher for SipHasher13 {
    #[inline]
    fn write(&mut self, msg: &[u8]) {
        dummy()
    }

    #[inline]
    fn finish(&self) -> u64 {
        dummy_val(0)
    }
}
