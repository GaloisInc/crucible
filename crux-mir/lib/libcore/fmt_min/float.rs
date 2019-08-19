use crate::fmt::{Formatter, Result, LowerExp, UpperExp, Display, Debug};
use super::dummy;

macro_rules! floating {
    ($ty:ident) => (
        #[stable(feature = "rust1", since = "1.0.0")]
        impl Debug for $ty {
            fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
                dummy()
            }
        }

        #[stable(feature = "rust1", since = "1.0.0")]
        impl Display for $ty {
            fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
                dummy()
            }
        }

        #[stable(feature = "rust1", since = "1.0.0")]
        impl LowerExp for $ty {
            fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
                dummy()
            }
        }

        #[stable(feature = "rust1", since = "1.0.0")]
        impl UpperExp for $ty {
            fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
                dummy()
            }
        }
    )
}

floating! { f32 }
floating! { f64 }
