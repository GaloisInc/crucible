#![feature(i128_type)]
#![crate_type = "lib"]
#![no_implicit_prelude]
#![feature(slice_get_slice)]

pub mod ops {

    /*
    pub mod index {
        
        use std::marker::Sized;

        pub trait Index<Idx: ?Sized> {
            /// The returned type after indexing.
            type Output: ?Sized;

            /// Performs the indexing (`container[index]`) operation.
            fn index(&self, index: Idx) -> &Self::Output;
        }
        
        pub trait IndexMut<Idx: ?Sized>: Index<Idx> {
            /// Performs the mutable indexing (`container[index]`) operation.
            fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
        }

    }

    use ops::index::Index;
    use ops::index::IndexMut;
    use std::slice::SliceIndex;

    impl<T, I> Index<I> for [T]
    where I: SliceIndex<[T]>
    {
        type Output = I::Output;
        
        #[inline]
        fn index(&self, index: I) -> &I::Output {
            index.index(self)
        }
    }

    impl<T, I> IndexMut<I> for [T]
    where I: SliceIndex<[T]>
    {
        #[inline]
        fn index_mut(&mut self, index: I) -> &mut I::Output {
            index.index_mut(self)
        }
    }
    */

}



pub mod slice {
    pub trait SliceIndex<T: ?Sized> {
        /// The output type returned by methods.
        type Output: ?Sized;

        /// Returns a shared reference to the output at this location, if in
        /// bounds.
        fn get(self, slice: &T) -> Option<&Self::Output>;

        /// Returns a mutable reference to the output at this location, if in
        /// bounds.
        fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;

        unsafe fn get_unchecked(self, slice: &T) -> &Self::Output;

        unsafe fn get_unchecked_mut(self, slice: &mut T) -> &mut Self::Output;
        
        /// Returns a shared reference to the output at this location, panicking
        /// if out of bounds.
        fn index(self, slice: &T) -> &Self::Output;

        /// Returns a mutable reference to the output at this location, panicking
        /// if out of bounds.
        fn index_mut(self, slice: &mut T) -> &mut Self::Output;
    }

    use std::marker::Sized;
    use std::option::Option;
    use std::option::Option::*;
    use std::ops::Range;
    use std::process::exit;

    /*
    impl<T>[T] {
        pub fn get<I>(&self, index: I) -> Option<&I::Output>
        where I: SliceIndex<Self>
        {
            index.get(self)
        }
    }*/


    

    #[inline(never)]
    #[cold]
    fn slice_index_len_fail(index: usize, len: usize) -> ! {
        //panic!("index {} out of range for slice of length {}", index, len);
        exit(0);
    }

    #[inline(never)]
    #[cold]
    fn slice_index_order_fail(index: usize, end: usize) -> ! {
        //panic!("slice index starts at {} but ends at {}", index, end);
        exit(0);
    }

    #[inline(never)]
    #[cold]
    fn slice_index_overflow_fail() -> ! {
        exit(0);
    }

    impl<T> SliceIndex<[T]> for usize {
        type Output = T;

        // SCW: we don't (yet) get the predicates when translating this op
        // so we'll make it primitive
        
        #[inline]
        fn get(self, slice: &[T]) -> Option<&T> {
            exit (0);
/*            if self < slice.len() {
                unsafe {
                    Some(self.get_unchecked(slice))
                }
            } else {
                None
            } */
        }

        #[inline]
        fn get_mut(self, slice: &mut [T]) -> Option<&mut T> {
            exit(0);
/*            
            if self < slice.len() {
                unsafe {
                    Some(self.get_unchecked_mut(slice))
                }
            } else {
                None
            } */
        }

        #[inline]
        unsafe fn get_unchecked(self, slice: &[T]) -> &T {
            exit(0);
        }

        #[inline]
        unsafe fn get_unchecked_mut(self, slice: &mut [T]) -> &mut T {
            exit(0);
        }

        #[inline]
        fn index(self, slice: &[T]) -> &T {
            // NB: use intrinsic indexing
            //&(*slice)[self]
            exit(0);
        }

        #[inline]
        fn index_mut(self, slice: &mut [T]) -> &mut T {
            // NB: use intrinsic indexing
            //&mut (*slice)[self]
            exit(0);
        }
    }
    /*
    impl<T> SliceIndex<[T]> for  Range<usize> {
        type Output = [T];

        #[inline]
        fn get(self, slice: &[T]) -> Option<&[T]> {
            if self.start > self.end || self.end > slice.len() {
                None
            } else {
                unsafe {
                    Some(self.get_unchecked(slice))
                }
            }
        }

        #[inline]
        fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
            if self.start > self.end || self.end > slice.len() {
                None
            } else {
                unsafe {
                    Some(self.get_unchecked_mut(slice))
                }
            }
        }

        #[inline]
        unsafe fn get_unchecked(self, slice: &[T]) -> &[T] {
            exit(0)
        }

        #[inline]
        unsafe fn get_unchecked_mut(self, slice: &mut [T]) -> &mut [T] {
            exit(0)
        }

        #[inline]
        fn index(self, slice: &[T]) -> &[T] {
            if self.start > self.end {
                slice_index_order_fail(self.start, self.end);
            } else if self.end > slice.len() {
                slice_index_len_fail(self.end, slice.len());
            }
            unsafe {
                self.get_unchecked(slice)
            }
        }

        #[inline]
        fn index_mut(self, slice: &mut [T]) -> &mut [T] {
            if self.start > self.end {
                slice_index_order_fail(self.start, self.end);
            } else if self.end > slice.len() {
                slice_index_len_fail(self.end, slice.len());
            }
            unsafe {
                self.get_unchecked_mut(slice)
            }
        }
    }*/


}

