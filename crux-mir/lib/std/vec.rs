use core::cmp::Ordering;
use core::convert::{From, AsRef, AsMut};
use core::default::Default;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::IntoIterator;
use core::mem;
use core::ops::{Deref, DerefMut};

use crucible::vector::Vector;

use crate::io;


#[derive(Clone)]
pub struct Vec<T> {
    data: Vector<T>,
}

impl<T> Vec<T> {
    pub fn new() -> Vec<T> {
        Vec { data: Vector::new() }
    }

    pub fn with_capacity(cap: usize) -> Vec<T> {
        Self::new()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn push(&mut self, x: T) {
        let old = mem::replace(&mut self.data, Vector::new());
        self.data = old.push(x);
    }

    pub fn pop(&mut self) -> Option<T> {
        let old = mem::replace(&mut self.data, Vector::new());
        let (new, x) = old.pop();
        self.data = new;
        x
    }

    // TODO: for performance, override extend_from_slice for Vec<u8>
    pub fn extend_from_slice(&mut self, slice: &[T])
    where T: Clone {
        for x in slice {
            self.push(x.clone());
        }
    }

    pub fn sort_by_key<K, F>(&mut self, mut f: F)
    where F: FnMut(&T) -> K, K: Ord {
        for i in 0 .. self.len() {
            let mut best_idx = i;
            let mut best_key = f(&self[i]);
            for j in i + 1 .. self.len() {
                let key = f(&self[j]);
                if key < best_key {
                    best_key = key;
                    best_idx = j;
                }
            }
            self.swap(i, best_idx);
        }
    }
}

impl<T: PartialEq> PartialEq for Vec<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        <[T] as PartialEq>::eq(self, other)
    }
    fn ne(&self, other: &Vec<T>) -> bool {
        <[T] as PartialEq>::ne(self, other)
    }
}

impl<T: PartialOrd> PartialOrd for Vec<T> {
    fn partial_cmp(&self, other: &Vec<T>) -> Option<Ordering> {
        <[T] as PartialOrd>::partial_cmp(self, other)
    }
    fn lt(&self, other: &Vec<T>) -> bool {
        <[T] as PartialOrd>::lt(self, other)
    }
    fn le(&self, other: &Vec<T>) -> bool {
        <[T] as PartialOrd>::le(self, other)
    }
    fn gt(&self, other: &Vec<T>) -> bool {
        <[T] as PartialOrd>::gt(self, other)
    }
    fn ge(&self, other: &Vec<T>) -> bool {
        <[T] as PartialOrd>::ge(self, other)
    }
}

impl<T: Eq> Eq for Vec<T> {}

impl<T: Ord> Ord for Vec<T> {
    fn cmp(&self, other: &Vec<T>) -> Ordering {
        <[T] as Ord>::cmp(self, other)
    }
}

impl<T: fmt::Debug> fmt::Debug for Vec<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        <[T] as fmt::Debug>::fmt(self, fmt)
    }
}

impl<T: Hash> Hash for Vec<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        <[T] as Hash>::hash(self, state)
    }
}

impl<T> Deref for Vec<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.data.as_slice()
    }
}

impl<T> DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.data.as_mut_slice()
    }
}

impl<T> Default for Vec<T> {
    fn default() -> Self {
        Vec::new()
    }
}

impl io::Write for Vec<u8> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl<T: Clone> From<&[T]> for Vec<T> {
    fn from(x: &[T]) -> Vec<T> {
        let mut v = Vec::with_capacity(x.len());
        v.extend_from_slice(x);
        v
    }
}

impl<T: Clone> From<&mut [T]> for Vec<T> {
    fn from(x: &mut [T]) -> Vec<T> {
        From::<&[T]>::from(x)
    }
}

pub struct IntoIter<T> {
    /// `vec` is the original vec, reversed.  So `next` is simply `vec.pop()`.
    vec: Vec<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.vec.pop()
    }
}

impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(mut self) -> IntoIter<T> {
        self.reverse();
        IntoIter { vec: self }
    }
}

impl<T> AsRef<[T]> for Vec<T> {
    fn as_ref(&self) -> &[T] { self }
}

impl<T> AsMut<[T]> for Vec<T> {
    fn as_mut(&mut self) -> &mut [T] { self }
}

impl<T> AsRef<Vec<T>> for Vec<T> {
    fn as_ref(&self) -> &Vec<T> { self }
}

impl<T> AsMut<Vec<T>> for Vec<T> {
    fn as_mut(&mut self) -> &mut Vec<T> { self }
}


#[macro_export]
macro_rules! vec {
    ($elem:expr; $n:expr) => (
        $crate::vec::from_elem($elem, $n)
    );
    ($($x:expr),*) => (
        {
            let mut v = Vec::new();
            $( v.push($x); )*
            v
        }
    );
    ($($x:expr,)*) => ($crate::vec![$($x),*])
}
