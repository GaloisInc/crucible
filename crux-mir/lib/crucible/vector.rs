//! This module exposes the Crucible `Vector` type to Rust.  From the Rust side, `Vector<T>`
//! behaves much like `[T; _]`, except that the length is not known at compile time.  However,
//! unlike `[T]`, `Vector<T>` is not considered a dynamically-sized type.  Yes, this is really
//! weird, but the only consumer of this type is our implementation of `std::vec::Vec`, so the
//! weirdness should be entirely hidden from most users.
use core::marker::PhantomData;


#[derive(Clone, Copy)]
pub struct Vector<T>(PhantomData<T>);

impl<T> Vector<T> {
    pub fn new() -> Vector<T> {
        unimplemented!("Vector::new")
    }

    pub fn len(&self) -> usize {
        unimplemented!("Vector::len")
    }

    pub fn push(self, x: T) -> Self {
        unimplemented!("Vector::push")
    }

    pub fn as_slice(&self) -> &[T] {
        unimplemented!("Vector::as_slice")
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unimplemented!("Vector::as_mut_slice")
    }
}
