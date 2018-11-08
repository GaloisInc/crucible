#![feature(i128_type)]
#![crate_type = "lib"]
#![no_implicit_prelude]


pub mod default {
    use std::marker::Sized;
    
    pub trait Default: Sized {
      fn default() -> Self;
    }

    macro_rules! default_impl {
        ($t:ty, $v:expr, $doc:tt) => {
            impl Default for $t {
                #[inline]
                #[doc = $doc]
                fn default() -> $t { $v }
            }
        }
    }


    default_impl! { (), (), "Returns the default value of `()`" }
    default_impl! { bool, false, "Returns the default value of `false`" }
    default_impl! { char, '\x00', "Returns the default value of `\\x00`" }
    
    default_impl! { usize, 0, "Returns the default value of `0`" }
    default_impl! { u8, 0, "Returns the default value of `0`" }
    default_impl! { u16, 0, "Returns the default value of `0`" }
    default_impl! { u32, 0, "Returns the default value of `0`" }
    default_impl! { u64, 0, "Returns the default value of `0`" }
    //default_impl! { u128, 0, "Returns the default value of `0`" }
    

    default_impl! { isize, 0, "Returns the default value of `0`" }
    default_impl! { i8, 0, "Returns the default value of `0`" }
    default_impl! { i16, 0, "Returns the default value of `0`" }
    default_impl! { i32, 0, "Returns the default value of `0`" }
    default_impl! { i64, 0, "Returns the default value of `0`" }
    //default_impl! { i128, 0, "Returns the default value of `0`" }

    //
    // mir-json doesn't handle float literals
    //
    //default_impl! { f32, 0.0f32, "Returns the default value of `0.0`" }
    //default_impl! { f64, 0.0f64, "Returns the default value of `0.0`" }
}

pub mod result {
    
    use option::Option;
    use option::Option::*;
    use result::Result::*;
    
    //use std::ops::FnOnce;

    pub enum Result<T, E> {
        /// Contains the success value
        Ok(T),

        /// Contains the error value
        Err(E),
    }

    
    impl<T, E> Result<T, E> {
        /////////////////////////////////////////////////////////////////////////
        // Querying the contained values
        /////////////////////////////////////////////////////////////////////////

        /// Returns `true` if the result is [`Ok`].
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// let x: Result<i32, &str> = Ok(-3);
        /// assert_eq!(x.is_ok(), true);
        ///
        /// let x: Result<i32, &str> = Err("Some error message");
        /// assert_eq!(x.is_ok(), false);
        /// ```
        #[inline]
        pub fn is_ok(&self) -> bool {
            match *self {
                Ok(_) => true,
                Err(_) => false
            }
        }

        /// Returns `true` if the result is [`Err`].
        ///
        /// [`Err`]: enum.Result.html#variant.Err
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// let x: Result<i32, &str> = Ok(-3);
        /// assert_eq!(x.is_err(), false);
        ///
        /// let x: Result<i32, &str> = Err("Some error message");
        /// assert_eq!(x.is_err(), true);
        /// ```
        #[inline]
        pub fn is_err(&self) -> bool {
            !self.is_ok()
        }

        
        /////////////////////////////////////////////////////////////////////////
        // Adapter for each variant
        /////////////////////////////////////////////////////////////////////////

        /// Converts from `Result<T, E>` to [`Option<T>`].
        ///
        /// Converts `self` into an [`Option<T>`], consuming `self`,
        /// and discarding the error, if any.
        ///
        /// [`Option<T>`]: ../../std/option/enum.Option.html
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// let x: Result<u32, &str> = Ok(2);
        /// assert_eq!(x.ok(), Some(2));
        ///
        /// let x: Result<u32, &str> = Err("Nothing here");
        /// assert_eq!(x.ok(), None);
        /// ```
        #[inline]
        pub fn ok(self) -> Option<T> {
            match self {
                Ok(x)  => Some(x),
                Err(_) => None,
            }
        }

        /// Converts from `Result<T, E>` to [`Option<E>`].
        ///
        /// Converts `self` into an [`Option<E>`], consuming `self`,
        /// and discarding the success value, if any.
        ///
        /// [`Option<E>`]: ../../std/option/enum.Option.html
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// let x: Result<u32, &str> = Ok(2);
        /// assert_eq!(x.err(), None);
        ///
        /// let x: Result<u32, &str> = Err("Nothing here");
        /// assert_eq!(x.err(), Some("Nothing here"));
        /// ```
        #[inline]
        pub fn err(self) -> Option<E> {
            match self {
                Ok(_)  => None,
                Err(x) => Some(x),
            }
        }

        /////////////////////////////////////////////////////////////////////////
        // Adapter for working with references
        /////////////////////////////////////////////////////////////////////////

        /// Converts from `Result<T, E>` to `Result<&T, &E>`.
        ///
        /// Produces a new `Result`, containing a reference
        /// into the original, leaving the original in place.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// let x: Result<u32, &str> = Ok(2);
        /// assert_eq!(x.as_ref(), Ok(&2));
        ///
        /// let x: Result<u32, &str> = Err("Error");
        /// assert_eq!(x.as_ref(), Err(&"Error"));
        /// ```
        #[inline]
        pub fn as_ref(&self) -> Result<&T, &E> {
            match *self {
                Ok(ref x) => Ok(x),
                Err(ref x) => Err(x),
            }
        }

/* Unexpected interior reference LProjection        
        /// Converts from `Result<T, E>` to `Result<&mut T, &mut E>`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// fn mutate(r: &mut Result<i32, i32>) {
        ///     match r.as_mut() {
        ///         Ok(v) => *v = 42,
        ///         Err(e) => *e = 0,
        ///     }
        /// }
        ///
        /// let mut x: Result<i32, i32> = Ok(2);
        /// mutate(&mut x);
        /// assert_eq!(x.unwrap(), 42);
        ///
        /// let mut x: Result<i32, i32> = Err(13);
        /// mutate(&mut x);
        /// assert_eq!(x.unwrap_err(), 0);
        /// ```
        #[inline]
        pub fn as_mut(&mut self) -> Result<&mut T, &mut E> {
            match *self {
                Ok(ref mut x) => Ok(x),
                Err(ref mut x) => Err(x),
            }
        }
*/
        /////////////////////////////////////////////////////////////////////////
        // Transforming contained values
        /////////////////////////////////////////////////////////////////////////

/*        /// Maps a `Result<T, E>` to `Result<U, E>` by applying a function to a
        /// contained [`Ok`] value, leaving an [`Err`] value untouched.
        ///
        /// This function can be used to compose the results of two functions.
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        /// [`Err`]: enum.Result.html#variant.Err
        ///
        /// # Examples
        ///
        /// Print the numbers on each line of a string multiplied by two.
        ///
        /// ```
        /// let line = "1\n2\n3\n4\n";
        ///
        /// for num in line.lines() {
        ///     match num.parse::<i32>().map(|i| i * 2) {
        ///         Ok(n) => println!("{}", n),
        ///         Err(..) => {}
        ///     }
        /// }
        /// ```
        #[inline]
        pub fn map<U, F: FnOnce(T) -> U>(self, op: F) -> Result<U,E> {
            match self {
                Ok(t) => Ok(op(t)),
                Err(e) => Err(e)
            }
        } 

        /// Maps a `Result<T, E>` to `U` by applying a function to a
        /// contained [`Ok`] value, or a fallback function to a
        /// contained [`Err`] value.
        ///
        /// This function can be used to unpack a successful result
        /// while handling an error.
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        /// [`Err`]: enum.Result.html#variant.Err
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// #![feature(result_map_or_else)]
        /// let k = 21;
        ///
        /// let x : Result<_, &str> = Ok("foo");
        /// assert_eq!(x.map_or_else(|e| k * 2, |v| v.len()), 3);
        ///
        /// let x : Result<&str, _> = Err("bar");
        /// assert_eq!(x.map_or_else(|e| k * 2, |v| v.len()), 42);
        /// ```
        #[inline]
        pub fn map_or_else<U, M: FnOnce(T) -> U, F: FnOnce(E) -> U>(self, fallback: F, map: M) -> U {
            self.map(map).unwrap_or_else(fallback)
        }

        /// Maps a `Result<T, E>` to `Result<T, F>` by applying a function to a
        /// contained [`Err`] value, leaving an [`Ok`] value untouched.
        ///
        /// This function can be used to pass through a successful result while handling
        /// an error.
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        /// [`Err`]: enum.Result.html#variant.Err
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// fn stringify(x: u32) -> String { format!("error code: {}", x) }
        ///
        /// let x: Result<u32, u32> = Ok(2);
        /// assert_eq!(x.map_err(stringify), Ok(2));
        ///
        /// let x: Result<u32, u32> = Err(13);
        /// assert_eq!(x.map_err(stringify), Err("error code: 13".to_string()));
        /// ```
        #[inline]
        pub fn map_err<F, O: FnOnce(E) -> F>(self, op: O) -> Result<T,F> {
            match self {
                Ok(t) => Ok(t),
                Err(e) => Err(op(e))
            }
        }
*/
        
        ////////////////////////////////////////////////////////////////////////
        // Boolean operations on the values, eager and lazy
        /////////////////////////////////////////////////////////////////////////

        /// Returns `res` if the result is [`Ok`], otherwise returns the [`Err`] value of `self`.
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        /// [`Err`]: enum.Result.html#variant.Err
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// let x: Result<u32, &str> = Ok(2);
        /// let y: Result<&str, &str> = Err("late error");
        /// assert_eq!(x.and(y), Err("late error"));
        ///
        /// let x: Result<u32, &str> = Err("early error");
        /// let y: Result<&str, &str> = Ok("foo");
        /// assert_eq!(x.and(y), Err("early error"));
        ///
        /// let x: Result<u32, &str> = Err("not a 2");
        /// let y: Result<&str, &str> = Err("late error");
        /// assert_eq!(x.and(y), Err("not a 2"));
        ///
        /// let x: Result<u32, &str> = Ok(2);
        /// let y: Result<&str, &str> = Ok("different result type");
        /// assert_eq!(x.and(y), Ok("different result type"));
        /// ```
        #[inline]
        
        pub fn and<U>(self, res: Result<U, E>) -> Result<U, E> {
            match self {
                Ok(_) => res,
                Err(e) => Err(e),
            }
        }

 /*       /// Calls `op` if the result is [`Ok`], otherwise returns the [`Err`] value of `self`.
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        /// [`Err`]: enum.Result.html#variant.Err
        ///
        /// This function can be used for control flow based on `Result` values.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// fn sq(x: u32) -> Result<u32, u32> { Ok(x * x) }
        /// fn err(x: u32) -> Result<u32, u32> { Err(x) }
        ///
        /// assert_eq!(Ok(2).and_then(sq).and_then(sq), Ok(16));
        /// assert_eq!(Ok(2).and_then(sq).and_then(err), Err(4));
        /// assert_eq!(Ok(2).and_then(err).and_then(sq), Err(2));
        /// assert_eq!(Err(3).and_then(sq).and_then(sq), Err(3));
        /// ```
        #[inline]       
        pub fn and_then<U, F: FnOnce(T) -> Result<U, E>>(self, op: F) -> Result<U, E> {
            match self {
                Ok(t) => op(t),
                Err(e) => Err(e),
            }
        } */

        /// Returns `res` if the result is [`Err`], otherwise returns the [`Ok`] value of `self`.
        ///
        /// Arguments passed to `or` are eagerly evaluated; if you are passing the
        /// result of a function call, it is recommended to use [`or_else`], which is
        /// lazily evaluated.
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        /// [`Err`]: enum.Result.html#variant.Err
        /// [`or_else`]: #method.or_else
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// let x: Result<u32, &str> = Ok(2);
        /// let y: Result<u32, &str> = Err("late error");
        /// assert_eq!(x.or(y), Ok(2));
        ///
        /// let x: Result<u32, &str> = Err("early error");
        /// let y: Result<u32, &str> = Ok(2);
        /// assert_eq!(x.or(y), Ok(2));
        ///
        /// let x: Result<u32, &str> = Err("not a 2");
        /// let y: Result<u32, &str> = Err("late error");
        /// assert_eq!(x.or(y), Err("late error"));
        ///
        /// let x: Result<u32, &str> = Ok(2);
        /// let y: Result<u32, &str> = Ok(100);
        /// assert_eq!(x.or(y), Ok(2));
        /// ```
        #[inline]
        
        pub fn or<F>(self, res: Result<T, F>) -> Result<T, F> {
            match self {
                Ok(v) => Ok(v),
                Err(_) => res,
            }
        }

/*        /// Calls `op` if the result is [`Err`], otherwise returns the [`Ok`] value of `self`.
        ///
        /// This function can be used for control flow based on result values.
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        /// [`Err`]: enum.Result.html#variant.Err
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// fn sq(x: u32) -> Result<u32, u32> { Ok(x * x) }
        /// fn err(x: u32) -> Result<u32, u32> { Err(x) }
        ///
        /// assert_eq!(Ok(2).or_else(sq).or_else(sq), Ok(2));
        /// assert_eq!(Ok(2).or_else(err).or_else(sq), Ok(2));
        /// assert_eq!(Err(3).or_else(sq).or_else(err), Ok(9));
        /// assert_eq!(Err(3).or_else(err).or_else(err), Err(3));
        /// ```
        #[inline]
        pub fn or_else<F, O: FnOnce(E) -> Result<T, F>>(self, op: O) -> Result<T, F> {
            match self {
                Ok(t) => Ok(t),
                Err(e) => op(e),
            }
        }
*/
        /// Unwraps a result, yielding the content of an [`Ok`].
        /// Else, it returns `optb`.
        ///
        /// Arguments passed to `unwrap_or` are eagerly evaluated; if you are passing
        /// the result of a function call, it is recommended to use [`unwrap_or_else`],
        /// which is lazily evaluated.
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        /// [`Err`]: enum.Result.html#variant.Err
        /// [`unwrap_or_else`]: #method.unwrap_or_else
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// let optb = 2;
        /// let x: Result<u32, &str> = Ok(9);
        /// assert_eq!(x.unwrap_or(optb), 9);
        ///
        /// let x: Result<u32, &str> = Err("error");
        /// assert_eq!(x.unwrap_or(optb), optb);
        /// ```
        #[inline]
        
        pub fn unwrap_or(self, optb: T) -> T {
            match self {
                Ok(t) => t,
                Err(_) => optb
            }
        }

/*        /// Unwraps a result, yielding the content of an [`Ok`].
        /// If the value is an [`Err`] then it calls `op` with its value.
        ///
        /// [`Ok`]: enum.Result.html#variant.Ok
        /// [`Err`]: enum.Result.html#variant.Err
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// fn count(x: &str) -> usize { x.len() }
        ///
        /// assert_eq!(Ok(2).unwrap_or_else(count), 2);
        /// assert_eq!(Err("foo").unwrap_or_else(count), 3);
        /// ```
        #[inline]
        pub fn unwrap_or_else<F: FnOnce(E) -> T>(self, op: F) -> T {
            match self {
                Ok(t) => t,
                Err(e) => op(e)
            }
        } */
    } 


}


pub mod option {

    use option::Option::*;
    use result::Result;
    use result::Result::*;
    
    //use std::clone::Clone;
    //use std::convert::From;
    //use std::iter::{FromIterator};
    //use std::iter::*;
    //use std::ops::FnOnce;

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

/*        #[inline]    
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
*/
        #[inline]
        pub fn ok_or<E>(self, err: E) -> Result<T, E> {
            match self {
                Some(v) => Ok(v),
                None => Err(err),
            }
        }
/*
        #[inline]
        pub fn ok_or_else<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E> {
            match self {
                Some(v) => Ok(v),
                None => Err(err()),
            }
        }
*/
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

/*        /// Returns [`None`] if the option is [`None`], otherwise calls `f` with the
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
        } */

/*        /// Returns `None` if the option is `None`, otherwise calls `predicate`
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
*/
      
        #[inline]
        
        pub fn or(self, optb: Option<T>) -> Option<T> {
            match self {
                Some(_) => self,
                None => optb,
            }
        }

/*        /// Returns the option if it contains a value, otherwise calls `f` and
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
*/
    }
}

pub mod cmp {
    // use self::Ordering::*;
    use std::marker::Sized;
    use option::Option;
    use option::Option::*;

/*    
    pub enum Ordering {
        /// An ordering where a compared value is less [than another].
        Less = -1,
        /// An ordering where a compared value is equal [to another].
        Equal = 0,
        /// An ordering where a compared value is greater [than another].
        Greater = 1,
    }

    impl Ordering {
        #[inline]
        pub fn reverse(self) -> Ordering {
            match self {
                Less => Greater,
                Equal => Equal,
                Greater => Less,
            }
        }

        #[inline]
        pub fn then(self, other: Ordering) -> Ordering {
            match self {
                Equal => other,
                _ => self,
            }
        }


        /* #[inline]
        pub fn then_with<F: FnOnce() -> Ordering>(self, f: F) -> Ordering {
            match self {
                Equal => f(),
                _ => self,
            }
        } */
    }

    /*
    impl PartialEq for Ordering {
        fn eq(&self, other: &Ordering) -> bool {
            (*self as i32).eq(&(*other as i32))
        }
    }
    
    impl Eq for Ordering {
    }


    impl Ord for Ordering {
    #[inline]
        fn cmp(&self, other: &Ordering) -> Ordering {
            (*self as i32).cmp(&(*other as i32))
        }
    }

    
    impl PartialOrd for Ordering {
        #[inline]
        fn partial_cmp(&self, other: &Ordering) -> Option<Ordering> {
            (*self as i32).partial_cmp(&(*other as i32))
        }
    }
    */

    /*
    pub trait PartialEq<Rhs: ?Sized = Self> {
        #[must_use]
        fn eq(&self, other: &Rhs) -> bool;
        
        #[inline]
        #[must_use]
        fn ne(&self, other: &Rhs) -> bool { !self.eq(other) }
    }

    pub trait Eq: PartialEq<Self> {
        // this method is used solely by #[deriving] to assert
        // that every component of a type implements #[deriving]
        // itself, the current deriving infrastructure means doing this
        // assertion without using a method on this trait is nearly
        // impossible.
        //
        // This should never be implemented by hand.
        #[doc(hidden)]
        #[inline]
        fn assert_receiver_is_total_eq(&self) {}
    }

    
    pub trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    
        #[must_use]
        fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;

  
        #[inline]
        #[must_use]
        fn lt(&self, other: &Rhs) -> bool {
            match self.partial_cmp(other) {
                Some(Less) => true,
                _ => false,
            }
        }

        #[inline]
        #[must_use]
        fn le(&self, other: &Rhs) -> bool {
            match self.partial_cmp(other) {
                Some(Less) | Some(Equal) => true,
                _ => false,
            }
        }

     
        #[inline]
        #[must_use]
        fn gt(&self, other: &Rhs) -> bool {
            match self.partial_cmp(other) {
                Some(Greater) => true,
                _ => false,
            }
        }

        #[inline]
        #[must_use]
        fn ge(&self, other: &Rhs) -> bool {
            match self.partial_cmp(other) {
                Some(Greater) | Some(Equal) => true,
                _ => false,
            }
        }
    }*/


    /*
    pub trait Ord: Eq + PartialOrd<Self> {
        fn cmp(&self, other: &Self) -> Ordering;
        fn max(self, other: Self) -> Self
        where Self: Sized {
            if other >= self { other } else { self }
        }

        fn min(self, other: Self) -> Self
        where Self: Sized {
            if self <= other { self } else { other }
        }
    }*/
*/
    
}


pub mod ops {
/*    
    mod function {
        pub trait FnOnce<Args> {
            type Output;

            fn call_once(self, args: Args) -> Self::Output;
        }

    }
    pub mod range {
        pub struct RangeFull;
        
        //#[derive(Clone, PartialEq, Eq, Hash)]  // not Copy -- see #27186
        pub struct Range<Idx> {
            /// The lower bound of the range (inclusive).
            pub start: Idx,
            /// The upper bound of the range (exclusive).            
            pub end: Idx,
        }


        pub struct RangeFrom<Idx> {
            /// The lower bound of the range (inclusive).
            pub start: Idx,
        }

        pub struct RangeTo<Idx> {
            /// The upper bound of the range (exclusive).
            pub end: Idx,
        }

        
    }
*/

}
