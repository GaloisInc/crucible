# bigint

[![Build Status](https://travis-ci.org/paritytech/bigint.svg?branch=master)](https://travis-ci.org/paritytech/bigint)

[API Documentation](https://docs.rs/bigint/)

## DEPRECATED
This crate is **deprecated** and will not be developed further.  Users are invited to prefer the [`uint`](https://crates.io/crates/uint) crate instead.

### Old readme:
Fixed-sized integers arithmetic

To specify a dependency, add to `Cargo.toml`

```toml
[dependencies]
bigint = "4"
```

Little example

```rust
extern crate bigint;
use bigint::U256;

fn main() {
	let mut val: U256 = 1023.into();
	for _ in 0..200 { val = val * 2.into() }
	assert_eq!(
		&format!("{}", val),
		"1643897619276947051879427220465009342380213662639797070513307648"
	);
}
```

### `no_std` crates

This crate has a feature, `std`, that is enabled by default. To use this crate
in a `no_std` context, add the following to your `Cargo.toml`:

```toml
[dependencies]
bigint = { version = "4", default-features = false }
```

# License

`bigint` is primarily distributed under the terms of both the MIT
license and the Apache License (Version 2.0), at your choice.

See LICENSE-APACHE, and LICENSE-MIT for details.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in `bigint` by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
