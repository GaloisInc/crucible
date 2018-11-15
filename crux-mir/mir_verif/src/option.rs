#![feature(i128_type)]
#![crate_type = "lib"]
#![no_implicit_prelude]

pub mod option {

    use option::Option::*;
    use std::result::Result;
    use std::result::Result::*;
    
    //use std::clone::Clone;
    //use std::convert::From;
    //use std::iter::{FromIterator};
    //use std::iter::*;
    use std::ops::FnOnce;

    pub enum Option<T> {
        /// No value
        None,
        /// Some value `T`
        Some(T)
    }
    
    impl<T> Option<T> {
        #[inline]    
        pub fn is_some(&self) -> bool {
            match *self {
                Some(_) => true,
                None => false,
            }
        }
        #[inline]
        pub fn is_none(&self) -> bool {
            !self.is_some()
        }

        #[inline]        
        pub fn as_ref(&self) -> Option<&T> {
            match *self {
                Some(ref x) => Some(x),
                None => None,
            }
        }
/* Unexpected interior reference LProjection
        #[inline]
        pub fn as_mut(&mut self) -> Option<&mut T> {
            match *self {
                Some(ref mut x) => Some(x),
                None => None,
            }
        }
         */
/* unknown lvalue access: Static        
        #[inline(never)]
        #[cold]
        pub fn expect_failed(msg: &str) -> ! {
            panic!("{}", msg)
        }
*/
        
/*        #[inline]
        pub fn expect(self, msg: &str) -> T {
            match self {
                Some(val) => val,
                None => expect_failed(msg),
            }
        }
         */
        
// CAN't handle static string        
/*        #[inline]
        pub fn unwrap(self) -> T {
            match self {
                Some(val) => val,
                None => panic!("called `Option::unwrap()` on a `None` value"),
            }
        }
*/
        #[inline]    
        pub fn unwrap_or(self, def: T) -> T {
            match self {
                Some(x) => x,
                None => def,
            }
        }

        #[inline]    
        pub fn unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T {
            match self {
                Some(x) => x,
                None => f(),
            }
        }

        #[inline]
        pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U> {
            match self {
                Some(x) => Some(f(x)),
                None => None,
            }
        }

        #[inline]
        pub fn map_or<U, F: FnOnce(T) -> U>(self, default: U, f: F) -> U {
            match self {
                Some(t) => f(t),
                None => default,
            }
        }
        #[inline]
        pub fn map_or_else<U, D: FnOnce() -> U, F: FnOnce(T) -> U>(self, default: D, f: F) -> U {
            match self {
                Some(t) => f(t),
                None => default(),
            }
        }

        #[inline]
        pub fn ok_or<E>(self, err: E) -> Result<T, E> {
            match self {
                Some(v) => Ok(v),
                None => Err(err),
            }
        }

        #[inline]
        pub fn ok_or_else<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E> {
            match self {
                Some(v) => Ok(v),
                None => Err(err()),
            }
        }

/*
        #[inline]
        pub fn iter(&self) -> Iter<T> {
            Iter { inner: Item { opt: self.as_ref() } }
        }

        #[inline]
        pub fn iter_mut(&mut self) -> IterMut<T> {
            IterMut { inner: Item { opt: self.as_mut() } }
    } */

        #[inline]
        pub fn and<U>(self, optb: Option<U>) -> Option<U> {
            match self {
                Some(_) => optb,
                None => None,
            }
        }

        /// Returns [`None`] if the option is [`None`], otherwise calls `f` with the
        /// wrapped value and returns the result.
        ///
        /// Some languages call this operation flatmap.
        ///
        /// [`None`]: #variant.None
        ///
        /// # Examples
        ///
        /// ```
        /// fn sq(x: u32) -> Option<u32> { Some(x * x) }
        /// fn nope(_: u32) -> Option<u32> { None }
        ///
        /// assert_eq!(Some(2).and_then(sq).and_then(sq), Some(16));
        /// assert_eq!(Some(2).and_then(sq).and_then(nope), None);
        /// assert_eq!(Some(2).and_then(nope).and_then(sq), None);
        /// assert_eq!(None.and_then(sq).and_then(sq), None);
        /// ```
        #[inline]
        pub fn and_then<U, F: FnOnce(T) -> Option<U>>(self, f: F) -> Option<U> {
            match self {
                Some(x) => f(x),
                None => None,
            }
        } 

        /// Returns `None` if the option is `None`, otherwise calls `predicate`
        /// with the wrapped value and returns:
        ///
        /// - `Some(t)` if `predicate` returns `true` (where `t` is the wrapped
        ///   value), and
        /// - `None` if `predicate` returns `false`.
        ///
        /// This function works similar to `Iterator::filter()`. You can imagine
        /// the `Option<T>` being an iterator over one or zero elements. `filter()`
        /// lets you decide which elements to keep.
        ///
        /// # Examples
        ///
        /// ```rust
        /// fn is_even(n: &i32) -> bool {
        ///     n % 2 == 0
        /// }
        ///
        /// assert_eq!(None.filter(is_even), None);
        /// assert_eq!(Some(3).filter(is_even), None);
        /// assert_eq!(Some(4).filter(is_even), Some(4));
        /// ```
        #[inline]
        pub fn filter<P: FnOnce(&T) -> bool>(self, predicate: P) -> Self {
            if let Some(x) = self {
                if predicate(&x) {
                    return Some(x)
                }
            }
            None
        }

      
        #[inline]
        
        pub fn or(self, optb: Option<T>) -> Option<T> {
            match self {
                Some(_) => self,
                None => optb,
            }
        }

        /// Returns the option if it contains a value, otherwise calls `f` and
        /// returns the result.
        ///
        /// # Examples
        ///
        /// ```
        /// fn nobody() -> Option<&'static str> { None }
        /// fn vikings() -> Option<&'static str> { Some("vikings") }
        ///
        /// assert_eq!(Some("barbarians").or_else(vikings), Some("barbarians"));
        /// assert_eq!(None.or_else(vikings), Some("vikings"));
        /// assert_eq!(None.or_else(nobody), None);
        /// ```
        #[inline]
        
        pub fn or_else<F: FnOnce() -> Option<T>>(self, f: F) -> Option<T> {
            match self {
                Some(_) => self,
                None => f(),
            }
        } 

    }
}
