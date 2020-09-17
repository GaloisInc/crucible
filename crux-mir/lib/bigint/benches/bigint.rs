// Copyright 2015-2017 Parity Technologies
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! benchmarking for bigint
//! should be started with:
//! ```bash
//! rustup run nightly cargo bench
//! ```

#![feature(test)]

extern crate test;
extern crate bigint;

use test::{Bencher, black_box};
use bigint::{U256, U512, U128};

#[bench]
fn u256_add(b: &mut Bencher) {
    b.iter(|| {
        let n = black_box(10000);
        let zero = black_box(U256::zero());
        (0..n).fold(zero, |old, new| {
            old.overflowing_add(U256::from(black_box(new))).0
        })
    });
}

#[bench]
fn u256_sub(b: &mut Bencher) {
    b.iter(|| {
        let n = black_box(10000);
        let max = black_box(U256::max_value());
        (0..n).fold(max, |old, new| {
            old.overflowing_sub(U256::from(black_box(new))).0
        })
    });
}

#[bench]
fn u512_sub(b: &mut Bencher) {
    b.iter(|| {
        let n = black_box(10000);
        let max = black_box(U512::max_value());
        (0..n).fold(max, |old, new| {
            let new = black_box(new);
            let p = new % 2;
            old.overflowing_sub(U512([p, p, p, p, p, p, p, new])).0
        })
    });
}

#[bench]
fn u512_add(b: &mut Bencher) {
    b.iter(|| {
        let n = black_box(10000);
        let zero = black_box(U512::zero());
        (0..n).fold(zero, |old, new| {
            let new = black_box(new);
            old.overflowing_add(U512([new, new, new, new, new, new, new, new]))
                .0
        })
    });
}

#[bench]
fn u512_mul(b: &mut Bencher) {
    b.iter(|| {
        (1..10000).fold(black_box(U512::one()), |old, new| {
            old.overflowing_mul(U512::from(black_box(new | 1))).0
        })
    });
}

#[bench]
fn u512_mul_small(b: &mut Bencher) {
    b.iter(|| {
        (1..153).fold(black_box(U512::one()), |old, _| {
            old.overflowing_mul(U512::from(black_box(10))).0
        })
    });
}

#[bench]
fn u256_mul(b: &mut Bencher) {
    b.iter(|| {
        (1..10000).fold(black_box(U256::one()), |old, new| {
            old.overflowing_mul(U256::from(black_box(new | 1))).0
        })
    });
}

#[bench]
fn u256_mul_small(b: &mut Bencher) {
    b.iter(|| {
        (1..77).fold(black_box(U256::one()), |old, _| {
            old.overflowing_mul(U256::from(black_box(10))).0
        })
    });
}

#[bench]
fn u256_full_mul(b: &mut Bencher) {
    b.iter(|| {
        let n = black_box(10000);
        let one = black_box(U256::one());
        (1..n).map(|n| n | 1).fold(one, |old, new| {
            let new = black_box(new);
            let U512(ref u512words) = old.full_mul(U256([new, new, new, new]));
            U256([u512words[0], u512words[2], u512words[2], u512words[3]])
        })
    });
}


#[bench]
fn u128_mul(b: &mut Bencher) {
    b.iter(|| {
        let n = black_box(10000);
        (1..n).fold(U128([12345u64, 0u64]), |old, new| {
            old.overflowing_mul(U128::from(new | 1)).0
        })
    });
}

#[bench]
fn u256_from_le(b: &mut Bencher) {
    b.iter(|| {
        let raw = black_box(
            [
                1u8,
                2,
                3,
                5,
                7,
                11,
                13,
                17,
                19,
                23,
                29,
                31,
                37,
                41,
                43,
                47,
                53,
                59,
                61,
                67,
                71,
                73,
                79,
                83,
                89,
                97,
                101,
                103,
                107,
                109,
                113,
                127,
            ],
        );
        let _ = U256::from_little_endian(&raw[..]);
    });
}

#[bench]
fn u256_from_be(b: &mut Bencher) {
    b.iter(|| {
        let raw = black_box(
            [
                1u8,
                2,
                3,
                5,
                7,
                11,
                13,
                17,
                19,
                23,
                29,
                31,
                37,
                41,
                43,
                47,
                53,
                59,
                61,
                67,
                71,
                73,
                79,
                83,
                89,
                97,
                101,
                103,
                107,
                109,
                113,
                127,
            ],
        );
        let _ = U256::from_big_endian(&raw[..]);
    });
}
