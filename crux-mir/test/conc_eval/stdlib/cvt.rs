
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
fn main() {
   println!("{:?}", f(ARG));
}
