#![crate_type = "lib"]
#![no_implicit_prelude]


pub mod cmp {
    use self::Ordering::*;
    
    use std::marker::Sized;
    use std::option::Option;
    use std::option::Option::*;
    use std::ops::FnOnce;


    pub trait PartialEq<Rhs: ?Sized = Self> {
    /// This method tests for `self` and `other` values to be equal, and is used
    /// by `==`.
        fn eq(&self, other: &Rhs) -> bool;

        fn ne(&self, other: &Rhs) -> bool; // { !self.eq(other) }
    }

    pub trait Eq: PartialEq<Self> {}
    
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

    // ----- Reverse ---------------------
/*
    pub struct Reverse<T>(pub T);
    
    impl<T: PartialEq> PartialEq for Reverse<T> {
        fn eq(&self, other:&Self) -> bool { other.0.eq(&self.0) }
        fn ne(&self,other:&Self) -> bool  { other.0.ne(&self.0) }
    }
    impl<T: Eq>  Eq for Reverse<T> {}
    
    impl<T: PartialOrd> PartialOrd for Reverse<T> {
        #[inline]
        fn partial_cmp(&self, other: &Reverse<T>) -> Option<Ordering> {
            other.0.partial_cmp(&self.0)
        }

        #[inline]
        fn lt(&self, other: &Self) -> bool { other.0.lt(&self.0) }
        #[inline]
        fn le(&self, other: &Self) -> bool { other.0.le(&self.0) }
        #[inline]
        fn ge(&self, other: &Self) -> bool { other.0.ge(&self.0) }
        #[inline]
        fn gt(&self, other: &Self) -> bool { other.0.gt(&self.0) }
    }

    impl<T: Ord> Ord for Reverse<T> {
        #[inline]
        fn cmp(&self, other: &Reverse<T>) -> Ordering {
            other.0.cmp(&self.0)
        }
    }
     */
    // ----- Ord ---------------------

    pub trait Ord: Eq + PartialOrd<Self> {
        fn cmp(&self, other: &Self) -> Ordering;
        fn max(self, other: Self) -> Self;
        /* where Self: Sized  {
            if other.ge (&self) { other } else { self }
        } */
        fn min(self, other: Self) -> Self;
        /* where Self: Sized; {
            if self.le (&other) { self } else { other }
        } */
    }


    // ----- Ordering ---------------------

    // no deriving.... and no default methods ...
    impl PartialEq for Ordering {
        fn eq(&self, _other:&Self) -> bool { false }
        fn ne(&self, other: &Self) -> bool { !self.eq(other) }
    } 
    
    impl Eq for Ordering {} 

    impl Ord for Ordering {
        #[inline]
        fn cmp(&self, other: &Ordering) -> Ordering {
            match self {
                Less => match other {
                    Less => Equal,
                    _    => Less
                },
                Equal => match other {
                    Less => Greater,
                    Equal => Equal,
                    Greater => Less,
                }
                Greater => match other {
                    Greater => Equal,
                    _       => Greater
                }
            }
        }
        fn max(self, other: Self) -> Self
         where Self: Sized  {
            if other.ge (&self) { other } else { self }
        } 
        fn min(self, other: Self) -> Self
         where Self: Sized {
            if self.le (&other) { self } else { other }
        } 
    }

    impl PartialOrd for Ordering {
        #[inline]
        fn partial_cmp(&self, other: &Ordering) -> Option<Ordering> {
            Some(self.cmp(other))
        }
        fn lt(&self, other: &Ordering) -> bool {
            match self.partial_cmp(other) {
                Some(Less) => true,
                _ => false,
            }
        }
        fn le(&self, other: &Ordering) -> bool {
            match self.partial_cmp(other) {
                Some(Less) | Some(Equal) => true,
                _ => false,
            }
        }
        fn gt(&self, other: &Ordering) -> bool {
            match self.partial_cmp(other) {
                Some(Greater) => true,
                _ => false,
            }
        }
        fn ge(&self, other: &Ordering) -> bool {
            match self.partial_cmp(other) {
                Some(Greater) | Some(Equal) => true,
                _ => false,
            }
        }
    }

    
    pub trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
        fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;
        
        fn lt(&self, other: &Rhs) -> bool; /* {
            match self.partial_cmp(other) {
                Some(Less) => true,
                _ => false,
            }
        } */
        fn le(&self, other: &Rhs) -> bool; /* {
            match self.partial_cmp(other) {
                Some(Less) | Some(Equal) => true,
                _ => false,
            }
        }*/
        fn gt(&self, other: &Rhs) -> bool; /* {
            match self.partial_cmp(other) {
                Some(Greater) => true,
                _ => false,
            }
        }*/
        fn ge(&self, other: &Rhs) -> bool; /* {
            match self.partial_cmp(other) {
                Some(Greater) | Some(Equal) => true,
                _ => false,
            }
        }*/
    }
    
/*
    pub fn min<T: Ord>(v1: T, v2: T) -> T {
        v1.min(v2)
    }
*/
    
}
