//! This module exposes the Crucible `Vector` type to Rust.  From the Rust side, `Vector<T>`
//! behaves much like `[T; _]`, except that the length is not known at compile time.  However,
//! unlike `[T]`, `Vector<T>` is not considered a dynamically-sized type.  Yes, this is really
//! weird, but the only consumer of this type is our implementation of `std::vec::Vec`, so the
//! weirdness should be entirely hidden from most users.
use core::marker::PhantomData;


#[derive(Copy)]
pub struct Vector<T>(u8, PhantomData<T>);

impl<T: Clone> Clone for Vector<T> {
    fn clone(&self) -> Self {
        Vector::clone_from_slice(self.as_slice())
    }
}

impl<T> Vector<T> {
    pub const fn new() -> Vector<T> {
        // This lets `new` be a `const fn`.  Unfortunately it also means
        // crux-mir will loop instead of crashing if it's ever run without
        // an override.
        Self::new()
    }

    pub fn len(&self) -> usize {
        unimplemented!("Vector::len")
    }

    pub fn push(self, x: T) -> Self {
        unimplemented!("Vector::push")
    }

    pub fn push_front(self, x: T) -> Self {
        unimplemented!("Vector::push_front")
    }

    pub fn pop(self) -> (Self, Option<T>) {
        unimplemented!("Vector::pop")
    }

    pub fn pop_front(self) -> (Option<T>, Self) {
        unimplemented!("Vector::pop_front")
    }

    pub fn as_slice(&self) -> &[T] {
        unimplemented!("Vector::as_slice")
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unimplemented!("Vector::as_mut_slice")
    }

    pub fn concat(self, other: Self) -> Self {
        unimplemented!("Vector::concat")
    }

    pub fn split_at(self, idx: usize) -> (Self, Self) {
        unimplemented!("Vector::split_at")
    }

    pub fn copy_from_slice(slice: &[T]) -> Self
    where T: Copy {
        unimplemented!("Vector::copy_from_slice")
    }

    pub fn clone_from_slice(slice: &[T]) -> Self
    where T: Clone {
        // TODO: this implementation is O(n^2), since the vector is reallocated on every `push`.
        // We could make this faster with a CustomOp implementation, or with a generic `unfold`
        // function.
        let mut v = Vector::new();
        for x in slice {
            v = v.push(x.clone());
        }
        v
    }

    pub fn replicate(x: T, n: usize) -> Self
    where T: Copy {
        unimplemented!("Vector::replicate")
    }
}
