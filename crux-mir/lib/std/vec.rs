use core::convert::From;
use core::default::Default;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use crate::io;


#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Vec<T> {
    _dummy: [usize; 3],
    _marker: PhantomData<T>,
}

impl<T> Vec<T> {
    pub fn new() -> Vec<T> {
        unimplemented!()
    }

    pub fn with_capacity(cap: usize) -> Vec<T> {
        Self::new()
    }

    pub fn len(&self) -> usize {
        unimplemented!()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn push(&mut self, x: T) {
        unimplemented!()
    }

    pub fn pop(&mut self) -> Option<T> {
        unimplemented!()
    }

    // TODO: for performance, override extend_from_slice for Vec<u8>
    pub fn extend_from_slice(&mut self, slice: &[T])
    where T: Clone {
        for x in slice {
            self.push(x.clone());
        }
    }
}

impl<T> Deref for Vec<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        unimplemented!()
    }
}

impl<T> DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unimplemented!()
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
