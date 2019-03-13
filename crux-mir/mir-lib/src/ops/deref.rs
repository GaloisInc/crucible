//SCW: created from https://github.com/rust-lang/rust/blob/master/src/libcore/ops/deref.rs
// 3/13/19
//added preamble and removed stability & lang annotations
#![crate_type = "lib"]
#![no_implicit_prelude]
#![feature(lang_items)]
#![feature(on_unimplemented)]
#![feature(doc_alias)]

use std::marker::Sized;

///
/// impl<T> Deref for DerefExample<T> {
///     type Target = T;
///
///     fn deref(&self) -> &T {
///         &self.value
///     }
/// }
///
/// let x = DerefExample { value: 'a' };
/// assert_eq!('a', *x);
/// ```

#[doc(alias = "*")]
#[doc(alias = "&*")]

pub trait Deref {
    /// The resulting type after dereferencing.

    type Target: ?Sized;

    /// Dereferences the value.
    #[must_use]

    fn deref(&self) -> &Self::Target;
}


impl<T: ?Sized> Deref for &T {
    type Target = T;

    fn deref(&self) -> &T { *self }
}


impl<T: ?Sized> Deref for &mut T {
    type Target = T;

    fn deref(&self) -> &T { *self }
}

/// Used for mutable dereferencing operations, like in `*v = 1;`.
///
/// In addition to being used for explicit dereferencing operations with the
/// (unary) `*` operator in mutable contexts, `DerefMut` is also used implicitly
/// by the compiler in many circumstances. This mechanism is called
/// ['`Deref` coercion'][more]. In immutable contexts, [`Deref`] is used.
///
/// Implementing `DerefMut` for smart pointers makes mutating the data behind
/// them convenient, which is why they implement `DerefMut`. On the other hand,
/// the rules regarding [`Deref`] and `DerefMut` were designed specifically to
/// accommodate smart pointers. Because of this, **`DerefMut` should only be
/// implemented for smart pointers** to avoid confusion.
///
/// For similar reasons, **this trait should never fail**. Failure during
/// dereferencing can be extremely confusing when `DerefMut` is invoked
/// implicitly.
///
/// # More on `Deref` coercion
///
/// If `T` implements `DerefMut<Target = U>`, and `x` is a value of type `T`,
/// then:
///
/// * In mutable contexts, `*x` on non-pointer types is equivalent to
///   `*DerefMut::deref_mut(&mut x)`.
/// * Values of type `&mut T` are coerced to values of type `&mut U`
/// * `T` implicitly implements all the (mutable) methods of the type `U`.
///
/// For more details, visit [the chapter in *The Rust Programming Language*]
/// [book] as well as the reference sections on [the dereference operator]
/// [ref-deref-op], [method resolution] and [type coercions].
///
/// [book]: ../../book/ch15-02-deref.html
/// [`Deref`]: trait.Deref.html
/// [more]: #more-on-deref-coercion
/// [ref-deref-op]: ../../reference/expressions/operator-expr.html#the-dereference-operator
/// [method resolution]: ../../reference/expressions/method-call-expr.html
/// [type coercions]: ../../reference/type-coercions.html
///
/// # Examples
///
/// A struct with a single field which is modifiable by dereferencing the
/// struct.
///
/// ```
/// use std::ops::{Deref, DerefMut};
///
/// struct DerefMutExample<T> {
///     value: T
/// }
///
/// impl<T> Deref for DerefMutExample<T> {
///     type Target = T;
///
///     fn deref(&self) -> &T {
///         &self.value
///     }
/// }
///
/// impl<T> DerefMut for DerefMutExample<T> {
///     fn deref_mut(&mut self) -> &mut T {
///         &mut self.value
///     }
/// }
///
/// let mut x = DerefMutExample { value: 'a' };
/// *x = 'b';
/// assert_eq!('b', *x);
/// ```

#[doc(alias = "*")]

pub trait DerefMut: Deref {
    /// Mutably dereferences the value.

    fn deref_mut(&mut self) -> &mut Self::Target;
}


impl<T: ?Sized> DerefMut for &mut T {
    fn deref_mut(&mut self) -> &mut T { *self }
}

/// Indicates that a struct can be used as a method receiver, without the
/// `arbitrary_self_types` feature. This is implemented by stdlib pointer types like `Box<T>`,
/// `Rc<T>`, `&T`, and `Pin<P>`.


#[doc(hidden)]
pub trait Receiver {
    // Empty.
}


impl<T: ?Sized> Receiver for &T {}


impl<T: ?Sized> Receiver for &mut T {}
