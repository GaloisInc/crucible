use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::{self, SizedTypeProperties};
use core::ptr::NonNull;
use core::{fmt, ptr};

use crate::alloc::{Allocator, Global};

use super::VecDeque;

/// A draining iterator over the elements of a `VecDeque`.
///
/// This `struct` is created by the [`drain`] method on [`VecDeque`]. See its
/// documentation for more.
///
/// [`drain`]: VecDeque::drain
#[stable(feature = "drain", since = "1.6.0")]
pub struct Drain<
    'a,
    T: 'a,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
> {
    // We can't just use a &mut VecDeque<T, A>, as that would make Drain invariant over T
    // and we want it to be covariant instead
    deque: NonNull<VecDeque<T, A>>,
    // drain_start is stored in deque.len
    drain_len: usize,
    // index into the logical array, not the physical one (always lies in [0..deque.len))
    idx: usize,
    // number of elements after the drain range
    tail_len: usize,
    remaining: usize,
    // Needed to make Drain covariant over T
    _marker: PhantomData<&'a T>,
}

impl<'a, T, A: Allocator> Drain<'a, T, A> {
    pub(super) unsafe fn new(
        deque: &'a mut VecDeque<T, A>,
        drain_start: usize,
        drain_len: usize,
    ) -> Self {
        let orig_len = mem::replace(&mut deque.len, drain_start);
        let tail_len = orig_len - drain_start - drain_len;
        Drain {
            deque: NonNull::from(deque),
            drain_len,
            idx: drain_start,
            tail_len,
            remaining: drain_len,
            _marker: PhantomData,
        }
    }

    // Only returns pointers to the slices, as that's
    // all we need to drop them. May only be called if `self.remaining != 0`.
    unsafe fn as_slices(&self) -> (*mut [T], *mut [T]) {
        unsafe {
            let deque = self.deque.as_ref();
            // FIXME: This is doing almost exactly the same thing as the else branch in `VecDeque::slice_ranges`.
            // Unfortunately, we can't just call `slice_ranges` here, as the deque's `len` is currently
            // just `drain_start`, so the range check would (almost) always panic. Between temporarily
            // adjusting the deques `len` to call `slice_ranges`, and just copy pasting the `slice_ranges`
            // implementation, this seemed like the less hacky solution, though it might be good to
            // find a better one in the future.

            // because `self.remaining != 0`, we know that `self.idx < deque.original_len`, so it's a valid
            // logical index.
            let wrapped_start = deque.to_physical_idx(self.idx);

            let head_len = deque.capacity() - wrapped_start;

            let (a_range, b_range) = if head_len >= self.remaining {
                (wrapped_start..wrapped_start + self.remaining, 0..0)
            } else {
                let tail_len = self.remaining - head_len;
                (wrapped_start..deque.capacity(), 0..tail_len)
            };

            // SAFETY: the range `self.idx..self.idx+self.remaining` lies strictly inside
            // the range `0..deque.original_len`. because of this, and because of the fact
            // that we acquire `a_range` and `b_range` exactly like `slice_ranges` would,
            // it's guaranteed that `a_range` and `b_range` represent valid ranges into
            // the deques buffer.
            (deque.buffer_range(a_range), deque.buffer_range(b_range))
        }
    }
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for Drain<'_, T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain")
            .field(&self.drain_len)
            .field(&self.idx)
            .field(&self.tail_len)
            .field(&self.remaining)
            .finish()
    }
}

#[stable(feature = "drain", since = "1.6.0")]
unsafe impl<T: Sync, A: Allocator + Sync> Sync for Drain<'_, T, A> {}
#[stable(feature = "drain", since = "1.6.0")]
unsafe impl<T: Send, A: Allocator + Send> Send for Drain<'_, T, A> {}

#[stable(feature = "drain", since = "1.6.0")]
impl<T, A: Allocator> Drop for Drain<'_, T, A> {
    fn drop(&mut self) {
        struct DropGuard<'r, 'a, T, A: Allocator>(&'r mut Drain<'a, T, A>);

        impl<'r, 'a, T, A: Allocator> Drop for DropGuard<'r, 'a, T, A> {
            fn drop(&mut self) {
                if self.0.remaining != 0 {
                    unsafe {
                        // SAFETY: We just checked that `self.remaining != 0`.
                        let (front, back) = self.0.as_slices();
                        ptr::drop_in_place(front);
                        ptr::drop_in_place(back);
                    }
                }

                let source_deque = unsafe { self.0.deque.as_mut() };

                let drain_start = source_deque.len();
                let drain_len = self.0.drain_len;
                let drain_end = drain_start + drain_len;

                let orig_len = self.0.tail_len + drain_end;

                if T::IS_ZST {
                    // no need to copy around any memory if T is a ZST
                    source_deque.len = orig_len - drain_len;
                    return;
                }

                let head_len = drain_start;
                let tail_len = self.0.tail_len;

                match (head_len, tail_len) {
                    (0, 0) => {
                        source_deque.head = 0;
                        source_deque.len = 0;
                    }
                    (0, _) => {
                        source_deque.head = source_deque.to_physical_idx(drain_len);
                        source_deque.len = orig_len - drain_len;
                    }
                    (_, 0) => {
                        source_deque.len = orig_len - drain_len;
                    }
                    _ => unsafe {
                        if head_len <= tail_len {
                            source_deque.wrap_copy(
                                source_deque.head,
                                source_deque.to_physical_idx(drain_len),
                                head_len,
                            );
                            source_deque.head = source_deque.to_physical_idx(drain_len);
                            source_deque.len = orig_len - drain_len;
                        } else {
                            source_deque.wrap_copy(
                                source_deque.to_physical_idx(head_len + drain_len),
                                source_deque.to_physical_idx(head_len),
                                tail_len,
                            );
                            source_deque.len = orig_len - drain_len;
                        }
                    },
                }
            }
        }

        let guard = DropGuard(self);
        if guard.0.remaining != 0 {
            unsafe {
                // SAFETY: We just checked that `self.remaining != 0`.
                let (front, back) = guard.0.as_slices();
                // since idx is a logical index, we don't need to worry about wrapping.
                guard.0.idx += front.len();
                guard.0.remaining -= front.len();
                ptr::drop_in_place(front);
                guard.0.remaining = 0;
                ptr::drop_in_place(back);
            }
        }

        // Dropping `guard` handles moving the remaining elements into place.
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl<T, A: Allocator> Iterator for Drain<'_, T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        if self.remaining == 0 {
            return None;
        }
        let wrapped_idx = unsafe { self.deque.as_ref().to_physical_idx(self.idx) };
        self.idx += 1;
        self.remaining -= 1;
        Some(unsafe { self.deque.as_mut().buffer_read(wrapped_idx) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.remaining;
        (len, Some(len))
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl<T, A: Allocator> DoubleEndedIterator for Drain<'_, T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let wrapped_idx = unsafe { self.deque.as_ref().to_physical_idx(self.idx + self.remaining) };
        Some(unsafe { self.deque.as_mut().buffer_read(wrapped_idx) })
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl<T, A: Allocator> ExactSizeIterator for Drain<'_, T, A> {}

#[stable(feature = "fused", since = "1.26.0")]
impl<T, A: Allocator> FusedIterator for Drain<'_, T, A> {}
