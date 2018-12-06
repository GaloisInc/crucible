#![feature(i128_type)]
#![crate_type = "lib"]
#![no_implicit_prelude]


pub mod cmp {
    use self::Ordering::*;
    use std::marker::Sized;
    use std::option::Option;
    use std::option::Option::*;
    use std::ops::FnOnce;
    
    pub enum Ordering {
        /// An ordering where a compared value is greater [than another].
        Greater = 1,
        /// An ordering where a compared value is equal [to another].
        Equal = 0,
        /// An ordering where a compared value is less [than another].
        Less = -1,

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


        
        pub fn then_with<F: FnOnce() -> Ordering>(self, f: F) -> Ordering {
            match self {
                Equal => f(),
                _ => self,
            }
        } 
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

    
}
