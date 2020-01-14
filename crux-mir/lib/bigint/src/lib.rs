// Copyright 2015-2017 Parity Technologies
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Efficient large, fixed-size big integers and hashes.

#![cfg_attr(not(feature="std"), no_std)]
#![cfg_attr(all(not(feature="std"), test), feature(alloc))]

extern crate byteorder;

#[cfg(feature="std")]
extern crate rustc_hex;

#[macro_use]
extern crate crunchy;

#[cfg(feature="heapsizeof")]
#[macro_use]
extern crate heapsize;

#[cfg(feature="serialize")]
extern crate serde;
#[cfg(feature="serialize")]
#[macro_use]
extern crate serde_derive;

#[cfg(feature="std")]
extern crate core;

#[cfg(all(feature = "std", test))]
#[macro_use]
extern crate quickcheck;

#[cfg(all(not(feature = "std"), test))]
#[macro_use]
extern crate alloc;

pub mod uint;
pub use ::uint::*;
