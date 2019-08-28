#![crate_name = "std"]
#![no_std]

pub mod io;

pub mod prelude {
    pub mod v1 {
        pub use core::prelude::v1::*;
    }
}
