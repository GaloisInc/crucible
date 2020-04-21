use core::iter::FusedIterator;
use core::ptr::{self, NonNull};
use core::{fmt, mem};

use super::{count, Iter, VecDeque};

/// A draining iterator over the elements of a `VecDeque`.
///
/// This `struct` is created by the [`drain`] method on [`VecDeque`]. See its
/// documentation for more.
///
/// [`drain`]: struct.VecDeque.html#method.drain
/// [`VecDeque`]: struct.VecDeque.html
#[stable(feature = "drain", since = "1.6.0")]
pub struct Drain<'a, T: 'a> {
    pub(crate) after_tail: usize,
    pub(crate) after_head: usize,
    pub(crate) iter: Iter<'a, T>,
    pub(crate) deque: NonNull<VecDeque<T>>,
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
        struct DropGuard<'r, 'a, T>(&'r mut Drain<'a, T>);

        impl<'r, 'a, T> Drop for DropGuard<'r, 'a, T> {
            fn drop(&mut self) {
                self.0.for_each(drop);

                let source_deque = unsafe { self.0.deque.as_mut() };

                // T = source_deque_tail; H = source_deque_head; t = drain_tail; h = drain_head
                //
                //        T   t   h   H
                // [. . . o o x x o o . . .]
                //
                let orig_tail = source_deque.tail;
                let drain_tail = source_deque.head;
                let drain_head = self.0.after_tail;
                let orig_head = self.0.after_head;

                let tail_len = count(orig_tail, drain_tail, source_deque.cap());
                let head_len = count(drain_head, orig_head, source_deque.cap());

                // Restore the original head value
                source_deque.head = orig_head;

                match (tail_len, head_len) {
                    (0, 0) => {
                        source_deque.head = 0;
                        source_deque.tail = 0;
                    }
                    (0, _) => {
                        source_deque.tail = drain_head;
                    }
                    (_, 0) => {
                        source_deque.head = drain_tail;
                    }
                    _ => unsafe {
                        if tail_len <= head_len {
                            source_deque.tail = source_deque.wrap_sub(drain_head, tail_len);
                            source_deque.wrap_copy(source_deque.tail, orig_tail, tail_len);
                        } else {
                            source_deque.head = source_deque.wrap_add(drain_tail, head_len);
                            source_deque.wrap_copy(drain_tail, drain_head, head_len);
                        }
                    },
                }
            }
        }

        while let Some(item) = self.next() {
            let guard = DropGuard(self);
            drop(item);
            mem::forget(guard);
        }

        DropGuard(self);
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
