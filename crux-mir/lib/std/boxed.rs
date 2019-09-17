use core::borrow::{Borrow, BorrowMut};
use core::cmp::Ordering;
use core::convert::{AsRef, AsMut};
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::{Deref, DerefMut, Receiver};
use core::ptr::Unique;


#[lang = "owned_box"]
#[fundamental]
pub struct Box<T: ?Sized>(Unique<T>);

impl<T> Box<T> {
    #[inline(always)]
    pub fn new(x: T) -> Box<T> {
        unimplemented!("Box::new")
    }
}


#[lang = "exchange_malloc"]
#[inline]
unsafe fn exchange_malloc(size: usize, align: usize) -> *mut u8 {
    unimplemented!()
}

#[lang = "box_free"]
#[inline]
unsafe fn box_free<T: ?Sized>(ptr: *mut T) {
    unimplemented!()
}

unsafe impl<#[may_dangle] T: ?Sized> Drop for Box<T> {
    fn drop(&mut self) {
        unimplemented!()
    }
}


impl<T: Default> Default for Box<T> {
    fn default() -> Box<T> {
        Box::new(T::default())
    }
}

impl<T: Clone> Clone for Box<T> {
    fn clone(&self) -> Box<T> {
        Box::new(T::clone(self))
    }

    fn clone_from(&mut self, other: &Box<T>) {
        T::clone_from(self, other)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Box<T> {
    fn eq(&self, other: &Box<T>) -> bool {
        T::eq(self, other)
    }
    fn ne(&self, other: &Box<T>) -> bool {
        T::ne(self, other)
    }
}

impl<T: ?Sized + PartialOrd> PartialOrd for Box<T> {
    fn partial_cmp(&self, other: &Box<T>) -> Option<Ordering> {
        T::partial_cmp(self, other)
    }
    fn lt(&self, other: &Box<T>) -> bool {
        T::lt(self, other)
    }
    fn le(&self, other: &Box<T>) -> bool {
        T::le(self, other)
    }
    fn gt(&self, other: &Box<T>) -> bool {
        T::gt(self, other)
    }
    fn ge(&self, other: &Box<T>) -> bool {
        T::ge(self, other)
    }
}

impl<T: ?Sized + Eq> Eq for Box<T> {
}

impl<T: ?Sized + Ord> Ord for Box<T> {
    fn cmp(&self, other: &Box<T>) -> Ordering {
        T::cmp(self, other)
    }
}

impl<T: ?Sized + Hash> Hash for Box<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        T::hash(self, state)
    }
}

impl<T> From<T> for Box<T> {
    fn from(x: T) -> Box<T> {
        Box::new(x)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Box<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Display>::fmt(self, fmt)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Box<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Debug>::fmt(self, fmt)
    }
}

impl<T: ?Sized> Deref for Box<T> {
    type Target = T;
    fn deref(&self) -> &T {
        self
    }
}

impl<T: ?Sized> DerefMut for Box<T> {
    fn deref_mut(&mut self) -> &mut T {
        self
    }
}

impl<T: ?Sized> Receiver for Box<T> {}

impl<T: ?Sized> Borrow<T> for Box<T> {
    fn borrow(&self) -> &T {
        self
    }
}

impl<T: ?Sized> BorrowMut<T> for Box<T> {
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

impl<T: ?Sized> AsRef<T> for Box<T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: ?Sized> AsMut<T> for Box<T> {
    fn as_mut(&mut self) -> &mut T {
        self
    }
}
