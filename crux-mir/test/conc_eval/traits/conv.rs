pub trait A<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Performs the conversion.
    fn try_into(self) -> Result<T, Self::Error>;
}

pub trait B<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Performs the conversion.
    fn try_from(value: T) -> Result<Self, Self::Error>;
}

impl<T, U> A<U> for T where U: B<T>
{
    type Error = U::Error;

    fn try_into(self) -> Result<U, U::Error> {
        U::try_from(self)
    }
}



fn f (y : u32) -> u32 { 
    y
}


const ARG: u32 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
