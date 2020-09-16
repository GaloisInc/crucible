use int::{Int, LargeInt};

macro_rules! udivmod_inner {
    ($n:expr, $d:expr, $rem:expr, $ty:ty) => {{
        let (n, d, rem) = ($n, $d, $rem);
        // NOTE X is unknown, K != 0
        if n.high() == 0 {
            if d.high() == 0 {
                // 0 X
                // ---
                // 0 X

                if let Some(rem) = rem {
                    *rem = <$ty>::from(n.low().aborting_rem(d.low()));
                }
                return <$ty>::from(n.low().aborting_div(d.low()))
            } else {
                // 0 X
                // ---
                // K X
                if let Some(rem) = rem {
                    *rem = n;
                }
                return 0;
            };
        }

        let mut sr;
        let mut q;
        let mut r;

        if d.low() == 0 {
            if d.high() == 0 {
                // K X
                // ---
                // 0 0
                // NOTE This should be unreachable in safe Rust because the program will panic before
                // this intrinsic is called
                ::abort();
            }

            if n.low() == 0 {
                // K 0
                // ---
                // K 0
                if let Some(rem) = rem {
                    *rem = <$ty>::from_parts(0, n.high().aborting_rem(d.high()));
                }
                return <$ty>::from(n.high().aborting_div(d.high()))
            }

            // K K
            // ---
            // K 0

            if d.high().is_power_of_two() {
                if let Some(rem) = rem {
                    *rem = <$ty>::from_parts(n.low(), n.high() & (d.high() - 1));
                }
                return <$ty>::from(n.high() >> d.high().trailing_zeros());
            }

            sr = d.high().leading_zeros().wrapping_sub(n.high().leading_zeros());

            // D > N
            if sr > <hty!($ty)>::BITS - 2 {
                if let Some(rem) = rem {
                    *rem = n;
                }
                return 0;
            }

            sr += 1;

            // 1 <= sr <= <hty!($ty)>::BITS - 1
            q = n << (<$ty>::BITS - sr);
            r = n >> sr;
        } else if d.high() == 0 {
            // K X
            // ---
            // 0 K
            if d.low().is_power_of_two() {
                if let Some(rem) = rem {
                    *rem = <$ty>::from(n.low() & (d.low() - 1));
                }

                if d.low() == 1 {
                    return n;
                } else {
                    let sr = d.low().trailing_zeros();
                    return n >> sr;
                };
            }

            sr = 1 + <hty!($ty)>::BITS + d.low().leading_zeros() - n.high().leading_zeros();

            // 2 <= sr <= u64::BITS - 1
            q = n << (<$ty>::BITS - sr);
            r = n >> sr;
        } else {
            // K X
            // ---
            // K K
            sr = d.high().leading_zeros().wrapping_sub(n.high().leading_zeros());

            // D > N
            if sr > <hty!($ty)>::BITS - 1 {
                if let Some(rem) = rem {
                    *rem = n;
                }
                return 0;
            }

            sr += 1;

            // 1 <= sr <= <hty!($ty)>::BITS
            q = n << (<$ty>::BITS - sr);
            r = n >> sr;
        }

        // Not a special case
        // q and r are initialized with
        // q = n << (u64::BITS - sr)
        // r = n >> sr
        // 1 <= sr <= u64::BITS - 1
        let mut carry = 0;

        // Don't use a range because they may generate references to memcpy in unoptimized code
        let mut i = 0;
        while i < sr {
            i += 1;

            // r:q = ((r:q) << 1) | carry
            r = (r << 1) | (q >> (<$ty>::BITS - 1));
            q = (q << 1) | carry as $ty;

            // carry = 0
            // if r >= d {
            //     r -= d;
            //     carry = 1;
            // }
            let s = (d.wrapping_sub(r).wrapping_sub(1)) as os_ty!($ty) >> (<$ty>::BITS - 1);
            carry = (s & 1) as hty!($ty);
            r -= d & s as $ty;
        }

        if let Some(rem) = rem {
            *rem = r;
        }
        (q << 1) | carry as $ty
    }}
}

intrinsics! {
    #[maybe_use_optimized_c_shim]
    #[arm_aeabi_alias = __aeabi_uidiv]
    /// Returns `n / d`
    pub extern "C" fn __udivsi3(n: u32, d: u32) -> u32 {
        // Special cases
        if d == 0 {
            // NOTE This should be unreachable in safe Rust because the program will panic before
            // this intrinsic is called
            ::abort();
        }

        if n == 0 {
            return 0;
        }

        let mut sr = d.leading_zeros().wrapping_sub(n.leading_zeros());

        // d > n
        if sr > u32::BITS - 1 {
            return 0;
        }

        // d == 1
        if sr == u32::BITS - 1 {
            return n;
        }

        sr += 1;

        // 1 <= sr <= u32::BITS - 1
        let mut q = n << (u32::BITS - sr);
        let mut r = n >> sr;

        let mut carry = 0;

        // Don't use a range because they may generate references to memcpy in unoptimized code
        let mut i = 0;
        while i < sr {
            i += 1;

            // r:q = ((r:q) << 1) | carry
            r = (r << 1) | (q >> (u32::BITS - 1));
            q = (q << 1) | carry;

            // carry = 0;
            // if r > d {
            //     r -= d;
            //     carry = 1;
            // }

            let s = (d.wrapping_sub(r).wrapping_sub(1)) as i32 >> (u32::BITS - 1);
            carry = (s & 1) as u32;
            r -= d & s as u32;
        }

        (q << 1) | carry
    }

    #[maybe_use_optimized_c_shim]
    /// Returns `n % d`
    pub extern "C" fn __umodsi3(n: u32, d: u32) -> u32 {
        let q = __udivsi3(n, d);
        n - q * d
    }

    #[maybe_use_optimized_c_shim]
    /// Returns `n / d` and sets `*rem = n % d`
    pub extern "C" fn __udivmodsi4(n: u32, d: u32, rem: Option<&mut u32>) -> u32 {
        let q = __udivsi3(n, d);
        if let Some(rem) = rem {
            *rem = n - (q * d);
        }
        q
    }

    #[maybe_use_optimized_c_shim]
    /// Returns `n / d`
    pub extern "C" fn __udivdi3(n: u64, d: u64) -> u64 {
        __udivmoddi4(n, d, None)
    }

    #[maybe_use_optimized_c_shim]
    /// Returns `n % d`
    pub extern "C" fn __umoddi3(n: u64, d: u64) -> u64 {
        let mut rem = 0;
        __udivmoddi4(n, d, Some(&mut rem));
        rem
    }

    #[win64_128bit_abi_hack]
    /// Returns `n / d`
    pub extern "C" fn __udivti3(n: u128, d: u128) -> u128 {
        __udivmodti4(n, d, None)
    }

    #[win64_128bit_abi_hack]
    /// Returns `n % d`
    pub extern "C" fn __umodti3(n: u128, d: u128) -> u128 {
        let mut rem = 0;
        __udivmodti4(n, d, Some(&mut rem));
        rem
    }

    /// Returns `n / d` and sets `*rem = n % d`
    pub extern "C" fn __udivmoddi4(n: u64, d: u64, rem: Option<&mut u64>) -> u64 {
        udivmod_inner!(n, d, rem, u64)
    }

    #[win64_128bit_abi_hack]
    /// Returns `n / d` and sets `*rem = n % d`
    pub extern "C" fn __udivmodti4(n: u128,
                                   d: u128,
                                   rem: Option<&mut u128>) -> u128 {
        udivmod_inner!(n, d, rem, u128)
    }
}
