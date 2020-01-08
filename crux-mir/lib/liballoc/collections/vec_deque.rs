//! A double-ended queue implemented with a growable ring buffer.
//!
//! This queue has `O(1)` amortized inserts and removals from both ends of the
//! container. It also has `O(1)` indexing like a vector. The contained elements
//! are not required to be copyable, and the queue will be sendable if the
//! contained type is sendable.

#![stable(feature = "rust1", since = "1.0.0")]

use core::array::LengthAtMost32;
use core::cmp::{self, Ordering};
use core::fmt;
use core::iter::{repeat_with, FromIterator, FusedIterator};
use core::mem;
use core::ops::Bound::{Excluded, Included, Unbounded};
use core::ops::{Index, IndexMut, RangeBounds, Try};
use core::ptr::{self, NonNull};
use core::slice;
use core::hash::{Hash, Hasher};

use crate::collections::CollectionAllocErr;
use crate::raw_vec::RawVec;
use crate::vec::Vec;

use crucible::crucible_assert_unreachable;
use crucible::vector::Vector;

#[cfg(test)]
mod tests;

const INITIAL_CAPACITY: usize = 7; // 2^3 - 1
const MINIMUM_CAPACITY: usize = 1; // 2 - 1
#[cfg(target_pointer_width = "16")]
const MAXIMUM_ZST_CAPACITY: usize = 1 << (16 - 1); // Largest possible power of two
#[cfg(target_pointer_width = "32")]
const MAXIMUM_ZST_CAPACITY: usize = 1 << (32 - 1); // Largest possible power of two
#[cfg(target_pointer_width = "64")]
const MAXIMUM_ZST_CAPACITY: usize = 1 << (64 - 1); // Largest possible power of two

/// A double-ended queue implemented with a growable ring buffer.
///
/// The "default" usage of this type as a queue is to use [`push_back`] to add to
/// the queue, and [`pop_front`] to remove from the queue. [`extend`] and [`append`]
/// push onto the back in this manner, and iterating over `VecDeque` goes front
/// to back.
///
/// [`push_back`]: #method.push_back
/// [`pop_front`]: #method.pop_front
/// [`extend`]: #method.extend
/// [`append`]: #method.append
#[stable(feature = "rust1", since = "1.0.0")]
pub struct VecDeque<T> {
    data: Vector<T>,
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Clone> Clone for VecDeque<T> {
    fn clone(&self) -> VecDeque<T> {
        self.iter().cloned().collect()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<#[may_dangle] T> Drop for VecDeque<T> {
    fn drop(&mut self) {
        let (front, back) = self.as_mut_slices();
        unsafe {
            // use drop for [T]
            ptr::drop_in_place(front);
            ptr::drop_in_place(back);
        }
        // RawVec handles deallocation
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Default for VecDeque<T> {
    /// Creates an empty `VecDeque<T>`.
    #[inline]
    fn default() -> VecDeque<T> {
        VecDeque::new()
    }
}

impl<T> VecDeque<T> {
    /// Creates an empty `VecDeque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let vector: VecDeque<u32> = VecDeque::new();
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn new() -> VecDeque<T> {
        VecDeque::with_capacity(INITIAL_CAPACITY)
    }

    /// Creates an empty `VecDeque` with space for at least `capacity` elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let vector: VecDeque<u32> = VecDeque::with_capacity(10);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn with_capacity(_capacity: usize) -> VecDeque<T> {
        VecDeque {
            data: Vector::new(),
        }
    }

    /// Convert this `VecDeque` into a raw `crucible::Vector`.
    #[unstable(feature = "crux", issue = "0")]
    pub fn into_crucible_vector(mut self) -> Vector<T> {
        mem::replace(&mut self.data, Vector::new())
    }

    /// Convert a raw `crucible::Vector` into a `VecDeque`.
    #[unstable(feature = "crux", issue = "0")]
    pub fn from_crucible_vector(v: Vector<T>) -> Self {
        VecDeque {
            data: v,
        }
    }

    /// Retrieves an element in the `VecDeque` by index.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// assert_eq!(buf.get(1), Some(&4));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.as_slice().get(index)
    }

    /// Retrieves an element in the `VecDeque` mutably by index.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// if let Some(elem) = buf.get_mut(1) {
    ///     *elem = 7;
    /// }
    ///
    /// assert_eq!(buf[1], 7);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.data.as_mut_slice().get_mut(index)
    }

    /// Swaps elements at indices `i` and `j`.
    ///
    /// `i` and `j` may be equal.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if either index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// assert_eq!(buf, [3, 4, 5]);
    /// buf.swap(0, 2);
    /// assert_eq!(buf, [5, 4, 3]);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn swap(&mut self, i: usize, j: usize) {
        self.data.as_mut_slice().swap(i, j);
    }

    /// Returns the number of elements the `VecDeque` can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let buf: VecDeque<i32> = VecDeque::with_capacity(10);
    /// assert!(buf.capacity() >= 10);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn capacity(&self) -> usize {
        self.data.len()
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to be inserted in the
    /// given `VecDeque`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests. Therefore
    /// capacity can not be relied upon to be precisely minimal. Prefer [`reserve`] if future
    /// insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<i32> = vec![1].into_iter().collect();
    /// buf.reserve_exact(10);
    /// assert!(buf.capacity() >= 11);
    /// ```
    ///
    /// [`reserve`]: #method.reserve
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve_exact(&mut self, additional: usize) {
        // No-op
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// `VecDeque`. The collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<i32> = vec![1].into_iter().collect();
    /// buf.reserve(10);
    /// assert!(buf.capacity() >= 11);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve(&mut self, additional: usize) {
        // No-op
    }

    /// Tries to reserves the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `VecDeque<T>`. After calling `reserve_exact`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer `reserve` if future insertions are expected.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(try_reserve)]
    /// use std::collections::CollectionAllocErr;
    /// use std::collections::VecDeque;
    ///
    /// fn process_data(data: &[u32]) -> Result<VecDeque<u32>, CollectionAllocErr> {
    ///     let mut output = VecDeque::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[unstable(feature = "try_reserve", reason = "new API", issue="48043")]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), CollectionAllocErr>  {
        Ok(())  // No-op
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given `VecDeque<T>`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(try_reserve)]
    /// use std::collections::CollectionAllocErr;
    /// use std::collections::VecDeque;
    ///
    /// fn process_data(data: &[u32]) -> Result<VecDeque<u32>, CollectionAllocErr> {
    ///     let mut output = VecDeque::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[unstable(feature = "try_reserve", reason = "new API", issue="48043")]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), CollectionAllocErr> {
        Ok(())  // No-op
    }

    /// Shrinks the capacity of the `VecDeque` as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator may still inform the
    /// `VecDeque` that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::with_capacity(15);
    /// buf.extend(0..4);
    /// assert_eq!(buf.capacity(), 15);
    /// buf.shrink_to_fit();
    /// assert!(buf.capacity() >= 4);
    /// ```
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn shrink_to_fit(&mut self) {
        // No-op
    }

    /// Shrinks the capacity of the `VecDeque` with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// Panics if the current capacity is smaller than the supplied
    /// minimum capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(shrink_to)]
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::with_capacity(15);
    /// buf.extend(0..4);
    /// assert_eq!(buf.capacity(), 15);
    /// buf.shrink_to(6);
    /// assert!(buf.capacity() >= 6);
    /// buf.shrink_to(0);
    /// assert!(buf.capacity() >= 4);
    /// ```
    #[unstable(feature = "shrink_to", reason = "new API", issue="56431")]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        // No-op
    }

    /// Shortens the `VecDeque`, dropping excess elements from the back.
    ///
    /// If `len` is greater than the `VecDeque`'s current length, this has no
    /// effect.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(10);
    /// buf.push_back(15);
    /// assert_eq!(buf, [5, 10, 15]);
    /// buf.truncate(1);
    /// assert_eq!(buf, [5]);
    /// ```
    #[stable(feature = "deque_extras", since = "1.16.0")]
    pub fn truncate(&mut self, len: usize) {
        for _ in len..self.len() {
            self.pop_back();
        }
    }

    /// Returns a front-to-back iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// let b: &[_] = &[&5, &3, &4];
    /// let c: Vec<&i32> = buf.iter().collect();
    /// assert_eq!(&c[..], b);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.data.as_slice().iter(),
        }
    }

    /// Returns a front-to-back iterator that returns mutable references.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// for num in buf.iter_mut() {
    ///     *num = *num - 2;
    /// }
    /// let b: &[_] = &[&mut 3, &mut 1, &mut 2];
    /// assert_eq!(&buf.iter_mut().collect::<Vec<&mut i32>>()[..], b);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            inner: self.data.as_mut_slice().iter_mut(),
        }
    }

    /// Returns a pair of slices which contain, in order, the contents of the
    /// `VecDeque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut vector = VecDeque::new();
    ///
    /// vector.push_back(0);
    /// vector.push_back(1);
    /// vector.push_back(2);
    ///
    /// assert_eq!(vector.as_slices(), (&[0, 1, 2][..], &[][..]));
    ///
    /// vector.push_front(10);
    /// vector.push_front(9);
    ///
    /// assert_eq!(vector.as_slices(), (&[9, 10][..], &[0, 1, 2][..]));
    /// ```
    #[inline]
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn as_slices(&self) -> (&[T], &[T]) {
        (self.data.as_slice(), &[])
    }

    /// Returns a pair of slices which contain, in order, the contents of the
    /// `VecDeque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut vector = VecDeque::new();
    ///
    /// vector.push_back(0);
    /// vector.push_back(1);
    ///
    /// vector.push_front(10);
    /// vector.push_front(9);
    ///
    /// vector.as_mut_slices().0[0] = 42;
    /// vector.as_mut_slices().1[0] = 24;
    /// assert_eq!(vector.as_slices(), (&[42, 10][..], &[24, 1][..]));
    /// ```
    #[inline]
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        (self.data.as_mut_slice(), &mut [])
    }

    /// Returns the number of elements in the `VecDeque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut v = VecDeque::new();
    /// assert_eq!(v.len(), 0);
    /// v.push_back(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns `true` if the `VecDeque` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut v = VecDeque::new();
    /// assert!(v.is_empty());
    /// v.push_front(1);
    /// assert!(!v.is_empty());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Creates a draining iterator that removes the specified range in the
    /// `VecDeque` and yields the removed items.
    ///
    /// Note 1: The element range is removed even if the iterator is not
    /// consumed until the end.
    ///
    /// Note 2: It is unspecified how many elements are removed from the deque,
    /// if the `Drain` value is not dropped, but the borrow it holds expires
    /// (e.g., due to `mem::forget`).
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut v: VecDeque<_> = vec![1, 2, 3].into_iter().collect();
    /// let drained = v.drain(2..).collect::<VecDeque<_>>();
    /// assert_eq!(drained, [3]);
    /// assert_eq!(v, [1, 2]);
    ///
    /// // A full range clears all contents
    /// v.drain(..);
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    #[stable(feature = "drain", since = "1.6.0")]
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T>
        where R: RangeBounds<usize>
    {
        crucible_assert_unreachable!()
    }

    /// Clears the `VecDeque`, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut v = VecDeque::new();
    /// v.push_back(1);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub fn clear(&mut self) {
        self.data = Vector::new();
    }

    /// Returns `true` if the `VecDeque` contains an element equal to the
    /// given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut vector: VecDeque<u32> = VecDeque::new();
    ///
    /// vector.push_back(0);
    /// vector.push_back(1);
    ///
    /// assert_eq!(vector.contains(&1), true);
    /// assert_eq!(vector.contains(&10), false);
    /// ```
    #[stable(feature = "vec_deque_contains", since = "1.12.0")]
    pub fn contains(&self, x: &T) -> bool
        where T: PartialEq<T>
    {
        let (a, b) = self.as_slices();
        a.contains(x) || b.contains(x)
    }

    /// Provides a reference to the front element, or `None` if the `VecDeque` is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// assert_eq!(d.front(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// assert_eq!(d.front(), Some(&1));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn front(&self) -> Option<&T> {
        if !self.is_empty() {
            Some(&self[0])
        } else {
            None
        }
    }

    /// Provides a mutable reference to the front element, or `None` if the
    /// `VecDeque` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// assert_eq!(d.front_mut(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// match d.front_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(d.front(), Some(&9));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        if !self.is_empty() {
            Some(&mut self[0])
        } else {
            None
        }
    }

    /// Provides a reference to the back element, or `None` if the `VecDeque` is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// assert_eq!(d.back(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// assert_eq!(d.back(), Some(&2));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn back(&self) -> Option<&T> {
        if !self.is_empty() {
            Some(&self[self.len() - 1])
        } else {
            None
        }
    }

    /// Provides a mutable reference to the back element, or `None` if the
    /// `VecDeque` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// assert_eq!(d.back(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// match d.back_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(d.back(), Some(&9));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        let len = self.len();
        if !self.is_empty() {
            Some(&mut self[len - 1])
        } else {
            None
        }
    }

    /// Removes the first element and returns it, or `None` if the `VecDeque` is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// d.push_back(1);
    /// d.push_back(2);
    ///
    /// assert_eq!(d.pop_front(), Some(1));
    /// assert_eq!(d.pop_front(), Some(2));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pop_front(&mut self) -> Option<T> {
        let old = mem::replace(&mut self.data, Vector::new());
        let (x, new) = old.pop_front();
        self.data = new;
        x
    }

    /// Prepends an element to the `VecDeque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// d.push_front(1);
    /// d.push_front(2);
    /// assert_eq!(d.front(), Some(&2));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn push_front(&mut self, value: T) {
        let old = mem::replace(&mut self.data, Vector::new());
        self.data = old.push_front(value);
    }

    /// Appends an element to the back of the `VecDeque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(1);
    /// buf.push_back(3);
    /// assert_eq!(3, *buf.back().unwrap());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn push_back(&mut self, value: T) {
        let old = mem::replace(&mut self.data, Vector::new());
        self.data = old.push(value);
    }

    /// Removes the last element from the `VecDeque` and returns it, or `None` if
    /// it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// assert_eq!(buf.pop_back(), None);
    /// buf.push_back(1);
    /// buf.push_back(3);
    /// assert_eq!(buf.pop_back(), Some(3));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pop_back(&mut self) -> Option<T> {
        let old = mem::replace(&mut self.data, Vector::new());
        let (new, x) = old.pop();
        self.data = new;
        x
    }

    #[inline]
    fn is_contiguous(&self) -> bool {
        true
    }

    /// Removes an element from anywhere in the `VecDeque` and returns it, replacing it with the
    /// last element.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// Returns `None` if `index` is out of bounds.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// assert_eq!(buf.swap_remove_back(0), None);
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// assert_eq!(buf.swap_remove_back(0), Some(1));
    /// assert_eq!(buf, [3, 2]);
    /// ```
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
        let length = self.len();
        if length > 0 && index < length - 1 {
            self.swap(index, length - 1);
        } else if index >= length {
            return None;
        }
        self.pop_back()
    }

    /// Removes an element from anywhere in the `VecDeque` and returns it,
    /// replacing it with the first element.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// Returns `None` if `index` is out of bounds.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// assert_eq!(buf.swap_remove_front(0), None);
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// assert_eq!(buf.swap_remove_front(2), Some(3));
    /// assert_eq!(buf, [2, 1]);
    /// ```
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        let length = self.len();
        if length > 0 && index < length && index != 0 {
            self.swap(index, 0);
        } else if index >= length {
            return None;
        }
        self.pop_front()
    }

    /// Inserts an element at `index` within the `VecDeque`, shifting all elements with indices
    /// greater than or equal to `index` towards the back.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than `VecDeque`'s length
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut vec_deque = VecDeque::new();
    /// vec_deque.push_back('a');
    /// vec_deque.push_back('b');
    /// vec_deque.push_back('c');
    /// assert_eq!(vec_deque, &['a', 'b', 'c']);
    ///
    /// vec_deque.insert(1, 'd');
    /// assert_eq!(vec_deque, &['a', 'd', 'b', 'c']);
    /// ```
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn insert(&mut self, index: usize, value: T) {
        crucible_assert_unreachable!()
    }

    /// Removes and returns the element at `index` from the `VecDeque`.
    /// Whichever end is closer to the removal point will be moved to make
    /// room, and all the affected elements will be moved to new positions.
    /// Returns `None` if `index` is out of bounds.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// assert_eq!(buf.remove(1), Some(2));
    /// assert_eq!(buf, [1, 3]);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn remove(&mut self, index: usize) -> Option<T> {
        crucible_assert_unreachable!()
    }

    /// Splits the `VecDeque` into two at the given index.
    ///
    /// Returns a newly allocated `VecDeque`. `self` contains elements `[0, at)`,
    /// and the returned `VecDeque` contains elements `[at, len)`.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<_> = vec![1,2,3].into_iter().collect();
    /// let buf2 = buf.split_off(1);
    /// assert_eq!(buf, [1]);
    /// assert_eq!(buf2, [2, 3]);
    /// ```
    #[inline]
    #[stable(feature = "split_off", since = "1.4.0")]
    pub fn split_off(&mut self, at: usize) -> Self {
        let old = mem::replace(&mut self.data, Vector::new());
        let (before, after) = old.split_at(at);
        self.data = before;
        VecDeque { data: after }
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the new number of elements in self overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<_> = vec![1, 2].into_iter().collect();
    /// let mut buf2: VecDeque<_> = vec![3, 4].into_iter().collect();
    /// buf.append(&mut buf2);
    /// assert_eq!(buf, [1, 2, 3, 4]);
    /// assert_eq!(buf2, []);
    /// ```
    #[inline]
    #[stable(feature = "append", since = "1.4.0")]
    pub fn append(&mut self, other: &mut Self) {
        let old = mem::replace(&mut self.data, Vector::new());
        self.data = old.concat(mem::replace(&mut other.data, Vector::new()));
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns false.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.extend(1..5);
    /// buf.retain(|&x| x%2 == 0);
    /// assert_eq!(buf, [2, 4]);
    /// ```
    ///
    /// The exact order may be useful for tracking external state, like an index.
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.extend(1..6);
    ///
    /// let keep = [false, true, true, false, true];
    /// let mut i = 0;
    /// buf.retain(|_| (keep[i], i += 1).0);
    /// assert_eq!(buf, [2, 3, 5]);
    /// ```
    #[stable(feature = "vec_deque_retain", since = "1.4.0")]
    pub fn retain<F>(&mut self, mut f: F)
        where F: FnMut(&T) -> bool
    {
        let len = self.len();
        let mut del = 0;
        for i in 0..len {
            if !f(&self[i]) {
                del += 1;
            } else if del > 0 {
                self.swap(i - del, i);
            }
        }
        if del > 0 {
            self.truncate(len - del);
        }
    }

    /// Modifies the `VecDeque` in-place so that `len()` is equal to `new_len`,
    /// either by removing excess elements from the back or by appending
    /// elements generated by calling `generator` to the back.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(10);
    /// buf.push_back(15);
    /// assert_eq!(buf, [5, 10, 15]);
    ///
    /// buf.resize_with(5, Default::default);
    /// assert_eq!(buf, [5, 10, 15, 0, 0]);
    ///
    /// buf.resize_with(2, || unreachable!());
    /// assert_eq!(buf, [5, 10]);
    ///
    /// let mut state = 100;
    /// buf.resize_with(5, || { state += 1; state });
    /// assert_eq!(buf, [5, 10, 101, 102, 103]);
    /// ```
    #[stable(feature = "vec_resize_with", since = "1.33.0")]
    pub fn resize_with(&mut self, new_len: usize, generator: impl FnMut()->T) {
        let len = self.len();

        if new_len > len {
            self.extend(repeat_with(generator).take(new_len - len))
        } else {
            self.truncate(new_len);
        }
    }

    /// Rotates the double-ended queue `mid` places to the left.
    ///
    /// Equivalently,
    /// - Rotates item `mid` into the first position.
    /// - Pops the first `mid` items and pushes them to the end.
    /// - Rotates `len() - mid` places to the right.
    ///
    /// # Panics
    ///
    /// If `mid` is greater than `len()`. Note that `mid == len()`
    /// does _not_ panic and is a no-op rotation.
    ///
    /// # Complexity
    ///
    /// Takes `O(min(mid, len() - mid))` time and no extra space.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<_> = (0..10).collect();
    ///
    /// buf.rotate_left(3);
    /// assert_eq!(buf, [3, 4, 5, 6, 7, 8, 9, 0, 1, 2]);
    ///
    /// for i in 1..10 {
    ///     assert_eq!(i * 3 % 10, buf[0]);
    ///     buf.rotate_left(3);
    /// }
    /// assert_eq!(buf, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// ```
    #[stable(feature = "vecdeque_rotate", since = "1.36.0")]
    pub fn rotate_left(&mut self, mid: usize) {
        assert!(mid <= self.len());
        let old = mem::replace(&mut self.data, Vector::new());
        let (before, after) = old.split_at(mid);
        self.data = after.concat(before);
    }

    /// Rotates the double-ended queue `k` places to the right.
    ///
    /// Equivalently,
    /// - Rotates the first item into position `k`.
    /// - Pops the last `k` items and pushes them to the front.
    /// - Rotates `len() - k` places to the left.
    ///
    /// # Panics
    ///
    /// If `k` is greater than `len()`. Note that `k == len()`
    /// does _not_ panic and is a no-op rotation.
    ///
    /// # Complexity
    ///
    /// Takes `O(min(k, len() - k))` time and no extra space.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<_> = (0..10).collect();
    ///
    /// buf.rotate_right(3);
    /// assert_eq!(buf, [7, 8, 9, 0, 1, 2, 3, 4, 5, 6]);
    ///
    /// for i in 1..10 {
    ///     assert_eq!(0, buf[i * 3 % 10]);
    ///     buf.rotate_right(3);
    /// }
    /// assert_eq!(buf, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// ```
    #[stable(feature = "vecdeque_rotate", since = "1.36.0")]
    pub fn rotate_right(&mut self, k: usize) {
        assert!(k <= self.len());
        self.rotate_left(self.len() - k);
    }
}

impl<T: Clone> VecDeque<T> {
    /// Modifies the `VecDeque` in-place so that `len()` is equal to new_len,
    /// either by removing excess elements from the back or by appending clones of `value`
    /// to the back.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(10);
    /// buf.push_back(15);
    /// assert_eq!(buf, [5, 10, 15]);
    ///
    /// buf.resize(2, 0);
    /// assert_eq!(buf, [5, 10]);
    ///
    /// buf.resize(5, 20);
    /// assert_eq!(buf, [5, 10, 20, 20, 20]);
    /// ```
    #[stable(feature = "deque_extras", since = "1.16.0")]
    pub fn resize(&mut self, new_len: usize, value: T) {
        self.resize_with(new_len, || value.clone());
    }
}

/// Calculate the number of elements left to be read in the buffer
#[inline]
fn count(tail: usize, head: usize, size: usize) -> usize {
    // size is always a power of 2
    (head.wrapping_sub(tail)) & (size - 1)
}

/// An iterator over the elements of a `VecDeque`.
///
/// This `struct` is created by the [`iter`] method on [`VecDeque`]. See its
/// documentation for more.
///
/// [`iter`]: struct.VecDeque.html#method.iter
/// [`VecDeque`]: struct.VecDeque.html
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Clone)]
pub struct Iter<'a, T: 'a> {
    inner: slice::Iter<'a, T>,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iter").finish()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        self.inner.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn fold<Acc, F>(self, mut accum: Acc, mut f: F) -> Acc
        where F: FnMut(Acc, Self::Item) -> Acc
    {
        self.inner.fold(accum, f)
    }

    fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Ok = B>,
    {
        self.inner.try_fold(init, f)
    }

    #[inline]
    fn last(self) -> Option<&'a T> {
        self.inner.last()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        self.inner.next_back()
    }

    fn rfold<Acc, F>(self, mut accum: Acc, mut f: F) -> Acc
        where F: FnMut(Acc, Self::Item) -> Acc
    {
        self.inner.rfold(accum, f)
    }

    fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Ok = B>,
    {
        self.inner.try_rfold(init, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> ExactSizeIterator for Iter<'_, T> {
    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for Iter<'_, T> {}


/// A mutable iterator over the elements of a `VecDeque`.
///
/// This `struct` is created by the [`iter_mut`] method on [`VecDeque`]. See its
/// documentation for more.
///
/// [`iter_mut`]: struct.VecDeque.html#method.iter_mut
/// [`VecDeque`]: struct.VecDeque.html
#[stable(feature = "rust1", since = "1.0.0")]
pub struct IterMut<'a, T: 'a> {
    inner: slice::IterMut<'a, T>,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug> fmt::Debug for IterMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IterMut").finish()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        self.inner.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn fold<Acc, F>(self, mut accum: Acc, mut f: F) -> Acc
        where F: FnMut(Acc, Self::Item) -> Acc
    {
        self.inner.fold(accum, f)
    }

    #[inline]
    fn last(mut self) -> Option<&'a mut T> {
        self.inner.last()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        self.inner.next_back()
    }

    fn rfold<Acc, F>(self, mut accum: Acc, mut f: F) -> Acc
        where F: FnMut(Acc, Self::Item) -> Acc
    {
        self.inner.rfold(accum, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> ExactSizeIterator for IterMut<'_, T> {
    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for IterMut<'_, T> {}

/// An owning iterator over the elements of a `VecDeque`.
///
/// This `struct` is created by the [`into_iter`] method on [`VecDeque`][`VecDeque`]
/// (provided by the `IntoIterator` trait). See its documentation for more.
///
/// [`into_iter`]: struct.VecDeque.html#method.into_iter
/// [`VecDeque`]: struct.VecDeque.html
#[derive(Clone)]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct IntoIter<T> {
    inner: VecDeque<T>,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug> fmt::Debug for IntoIter<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIter")
         .field(&self.inner)
         .finish()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.inner.len();
        (len, Some(len))
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.inner.pop_back()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> ExactSizeIterator for IntoIter<T> {
    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for IntoIter<T> {}

/// A draining iterator over the elements of a `VecDeque`.
///
/// This `struct` is created by the [`drain`] method on [`VecDeque`]. See its
/// documentation for more.
///
/// [`drain`]: struct.VecDeque.html#method.drain
/// [`VecDeque`]: struct.VecDeque.html
#[stable(feature = "drain", since = "1.6.0")]
pub struct Drain<'a, T: 'a> {
    after_tail: usize,
    after_head: usize,
    iter: Iter<'a, T>,
    deque: NonNull<VecDeque<T>>,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug> fmt::Debug for Drain<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain")
         .field(&self.after_tail)
         .field(&self.after_head)
         .field(&self.iter)
         .finish()
    }
}

#[stable(feature = "drain", since = "1.6.0")]
unsafe impl<T: Sync> Sync for Drain<'_, T> {}
#[stable(feature = "drain", since = "1.6.0")]
unsafe impl<T: Send> Send for Drain<'_, T> {}

#[stable(feature = "drain", since = "1.6.0")]
impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        crucible_assert_unreachable!();
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter.next().map(|elt| unsafe { ptr::read(elt) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl<T> DoubleEndedIterator for Drain<'_, T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back().map(|elt| unsafe { ptr::read(elt) })
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl<T> ExactSizeIterator for Drain<'_, T> {}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for Drain<'_, T> {}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A: PartialEq> PartialEq for VecDeque<A> {
    fn eq(&self, other: &VecDeque<A>) -> bool {
        if self.len() != other.len() {
            return false;
        }
        let (sa, sb) = self.as_slices();
        let (oa, ob) = other.as_slices();
        if sa.len() == oa.len() {
            sa == oa && sb == ob
        } else if sa.len() < oa.len() {
            // Always divisible in three sections, for example:
            // self:  [a b c|d e f]
            // other: [0 1 2 3|4 5]
            // front = 3, mid = 1,
            // [a b c] == [0 1 2] && [d] == [3] && [e f] == [4 5]
            let front = sa.len();
            let mid = oa.len() - front;

            let (oa_front, oa_mid) = oa.split_at(front);
            let (sb_mid, sb_back) = sb.split_at(mid);
            debug_assert_eq!(sa.len(), oa_front.len());
            debug_assert_eq!(sb_mid.len(), oa_mid.len());
            debug_assert_eq!(sb_back.len(), ob.len());
            sa == oa_front && sb_mid == oa_mid && sb_back == ob
        } else {
            let front = oa.len();
            let mid = sa.len() - front;

            let (sa_front, sa_mid) = sa.split_at(front);
            let (ob_mid, ob_back) = ob.split_at(mid);
            debug_assert_eq!(sa_front.len(), oa.len());
            debug_assert_eq!(sa_mid.len(), ob_mid.len());
            debug_assert_eq!(sb.len(), ob_back.len());
            sa_front == oa && sa_mid == ob_mid && sb == ob_back
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A: Eq> Eq for VecDeque<A> {}

macro_rules! __impl_slice_eq1 {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty, $($constraints:tt)*) => {
        #[stable(feature = "vec_deque_partial_eq_slice", since = "1.17.0")]
        impl<A, B, $($vars)*> PartialEq<$rhs> for $lhs
        where
            A: PartialEq<B>,
            $($constraints)*
        {
            fn eq(&self, other: &$rhs) -> bool {
                if self.len() != other.len() {
                    return false;
                }
                let (sa, sb) = self.as_slices();
                let (oa, ob) = other[..].split_at(sa.len());
                sa == oa && sb == ob
            }
        }
    }
}

__impl_slice_eq1! { [] VecDeque<A>, Vec<B>, }
__impl_slice_eq1! { [] VecDeque<A>, &[B], }
__impl_slice_eq1! { [] VecDeque<A>, &mut [B], }
__impl_slice_eq1! { [const N: usize] VecDeque<A>, [B; N], [B; N]: LengthAtMost32 }
__impl_slice_eq1! { [const N: usize] VecDeque<A>, &[B; N], [B; N]: LengthAtMost32 }
__impl_slice_eq1! { [const N: usize] VecDeque<A>, &mut [B; N], [B; N]: LengthAtMost32 }

#[stable(feature = "rust1", since = "1.0.0")]
impl<A: PartialOrd> PartialOrd for VecDeque<A> {
    fn partial_cmp(&self, other: &VecDeque<A>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A: Ord> Ord for VecDeque<A> {
    #[inline]
    fn cmp(&self, other: &VecDeque<A>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A: Hash> Hash for VecDeque<A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        let (a, b) = self.as_slices();
        Hash::hash_slice(a, state);
        Hash::hash_slice(b, state);
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A> Index<usize> for VecDeque<A> {
    type Output = A;

    #[inline]
    fn index(&self, index: usize) -> &A {
        self.get(index).expect("Out of bounds access")
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A> IndexMut<usize> for VecDeque<A> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut A {
        self.get_mut(index).expect("Out of bounds access")
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A> FromIterator<A> for VecDeque<A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> VecDeque<A> {
        let iterator = iter.into_iter();
        let (lower, _) = iterator.size_hint();
        let mut deq = VecDeque::with_capacity(lower);
        deq.extend(iterator);
        deq
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> IntoIterator for VecDeque<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Consumes the `VecDeque` into a front-to-back iterator yielding elements by
    /// value.
    fn into_iter(self) -> IntoIter<T> {
        IntoIter { inner: self }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> IntoIterator for &'a VecDeque<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> IntoIterator for &'a mut VecDeque<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A> Extend<A> for VecDeque<A> {
    fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T) {
        iter.into_iter().for_each(move |elt| self.push_back(elt));
    }
}

#[stable(feature = "extend_ref", since = "1.2.0")]
impl<'a, T: 'a + Copy> Extend<&'a T> for VecDeque<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Debug> fmt::Debug for VecDeque<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

#[stable(feature = "vecdeque_vec_conversions", since = "1.10.0")]
impl<T> From<Vec<T>> for VecDeque<T> {
    /// Turn a [`Vec<T>`] into a [`VecDeque<T>`].
    ///
    /// [`Vec<T>`]: crate::vec::Vec
    /// [`VecDeque<T>`]: crate::collections::VecDeque
    ///
    /// This avoids reallocating where possible, but the conditions for that are
    /// strict, and subject to change, and so shouldn't be relied upon unless the
    /// `Vec<T>` came from `From<VecDeque<T>>` and hasn't been reallocated.
    fn from(mut other: Vec<T>) -> Self {
        Self::from_crucible_vector(other.into_crucible_vector())
    }
}

#[stable(feature = "vecdeque_vec_conversions", since = "1.10.0")]
impl<T> From<VecDeque<T>> for Vec<T> {
    /// Turn a [`VecDeque<T>`] into a [`Vec<T>`].
    ///
    /// [`Vec<T>`]: crate::vec::Vec
    /// [`VecDeque<T>`]: crate::collections::VecDeque
    ///
    /// This never needs to re-allocate, but does need to do O(n) data movement if
    /// the circular buffer doesn't happen to be at the beginning of the allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// // This one is O(1).
    /// let deque: VecDeque<_> = (1..5).collect();
    /// let ptr = deque.as_slices().0.as_ptr();
    /// let vec = Vec::from(deque);
    /// assert_eq!(vec, [1, 2, 3, 4]);
    /// assert_eq!(vec.as_ptr(), ptr);
    ///
    /// // This one needs data rearranging.
    /// let mut deque: VecDeque<_> = (1..5).collect();
    /// deque.push_front(9);
    /// deque.push_front(8);
    /// let ptr = deque.as_slices().1.as_ptr();
    /// let vec = Vec::from(deque);
    /// assert_eq!(vec, [8, 9, 1, 2, 3, 4]);
    /// assert_eq!(vec.as_ptr(), ptr);
    /// ```
    fn from(other: VecDeque<T>) -> Self {
        Self::from_crucible_vector(other.into_crucible_vector())
    }
}
