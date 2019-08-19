// ignore-tidy-filelength

//! Stripped-down implementation of `core::str`.  Provides only the bare essentials used by other
//! parts of `core`.

#![stable(feature = "rust1", since = "1.0.0")]

use crate::char;
use crate::fmt::{self, Write};
use crate::iter::{Map, Cloned, FusedIterator, TrustedLen, TrustedRandomAccess, Filter};
use crate::iter::{Flatten, FlatMap, Chain};
use crate::slice::{self, SliceIndex, Split as SliceSplit};
use crate::mem;
use crate::ops::Try;
use crate::option;

#[lang = "str"]
#[cfg(not(test))]
impl str {
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    #[rustc_const_unstable(feature = "const_str_len")]
    pub const fn len(&self) -> usize {
        self.as_bytes().len()
    }

    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_unstable(feature = "const_str_len")]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline(always)]
    #[rustc_const_unstable(feature="const_str_as_bytes")]
    pub const fn as_bytes(&self) -> &[u8] {
        union Slices<'a> {
            str: &'a str,
            slice: &'a [u8],
        }
        unsafe { Slices { str: self }.slice }
    }
}

mod traits {
    use crate::cmp::Ordering;
    use crate::ops;
    use crate::slice::{self, SliceIndex};

    #[stable(feature = "rust1", since = "1.0.0")]
    impl Ord for str {
        #[inline]
        fn cmp(&self, other: &str) -> Ordering {
            self.as_bytes().cmp(other.as_bytes())
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl PartialEq for str {
        #[inline]
        fn eq(&self, other: &str) -> bool {
            self.as_bytes() == other.as_bytes()
        }
        #[inline]
        fn ne(&self, other: &str) -> bool { !(*self).eq(other) }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl Eq for str {}

    #[stable(feature = "rust1", since = "1.0.0")]
    impl PartialOrd for str {
        #[inline]
        fn partial_cmp(&self, other: &str) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
}
