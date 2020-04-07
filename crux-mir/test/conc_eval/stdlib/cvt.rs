#![cfg_attr(not(with_main), no_std)]

pub enum R<T, E> { X (T,E) }


pub trait TI<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Performs the conversion.
    fn try_into(self) -> R<T, Self::Error>;
}


fn f(_: ()) -> u32 {
    0 
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
