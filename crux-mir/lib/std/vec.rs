use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

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
