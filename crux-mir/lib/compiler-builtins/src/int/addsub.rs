use int::Int;
use int::LargeInt;

trait UAddSub: LargeInt {
    fn uadd(self, other: Self) -> Self {
        let (low, carry) = self.low().overflowing_add(other.low());
        let high = self.high().wrapping_add(other.high());
        let carry = if carry {
            Self::HighHalf::ONE
        } else {
            Self::HighHalf::ZERO
        };
        Self::from_parts(low, high.wrapping_add(carry))
    }
    fn uadd_one(self) -> Self {
        let (low, carry) = self.low().overflowing_add(Self::LowHalf::ONE);
        let carry = if carry {
            Self::HighHalf::ONE
        } else {
            Self::HighHalf::ZERO
        };
        Self::from_parts(low, self.high().wrapping_add(carry))
    }
    fn usub(self, other: Self) -> Self {
        let uneg = (!other).uadd_one();
        self.uadd(uneg)
    }
}

impl UAddSub for u128 {}

trait AddSub: Int
where
    <Self as Int>::UnsignedInt: UAddSub,
{
    fn add(self, other: Self) -> Self {
        Self::from_unsigned(self.unsigned().uadd(other.unsigned()))
    }
    fn sub(self, other: Self) -> Self {
        Self::from_unsigned(self.unsigned().usub(other.unsigned()))
    }
}

impl AddSub for u128 {}
impl AddSub for i128 {}

trait Addo: AddSub
where
    <Self as Int>::UnsignedInt: UAddSub,
{
    fn addo(self, other: Self, overflow: &mut i32) -> Self {
        *overflow = 0;
        let result = AddSub::add(self, other);
        if other >= Self::ZERO {
            if result < self {
                *overflow = 1;
            }
        } else {
            if result >= self {
                *overflow = 1;
            }
        }
        result
    }
}

impl Addo for i128 {}
impl Addo for u128 {}

trait Subo: AddSub
where
    <Self as Int>::UnsignedInt: UAddSub,
{
    fn subo(self, other: Self, overflow: &mut i32) -> Self {
        *overflow = 0;
        let result = AddSub::sub(self, other);
        if other >= Self::ZERO {
            if result > self {
                *overflow = 1;
            }
        } else {
            if result <= self {
                *overflow = 1;
            }
        }
        result
    }
}

impl Subo for i128 {}
impl Subo for u128 {}

intrinsics! {
    pub extern "C" fn __rust_i128_add(a: i128, b: i128) -> i128 {
        __rust_u128_add(a as _, b as _) as _
    }

    pub extern "C" fn __rust_i128_addo(a: i128, b: i128) -> (i128, bool) {
        let mut oflow = 0;
        let r = a.addo(b, &mut oflow);
        (r, oflow != 0)
    }

    pub extern "C" fn __rust_u128_add(a: u128, b: u128) -> u128 {
        a.add(b)
    }

    pub extern "C" fn __rust_u128_addo(a: u128, b: u128) -> (u128, bool) {
        let mut oflow = 0;
        let r = a.addo(b, &mut oflow);
        (r, oflow != 0)
    }


    pub extern "C" fn __rust_i128_sub(a: i128, b: i128) -> i128 {
        __rust_u128_sub(a as _, b as _) as _
    }

    pub extern "C" fn __rust_i128_subo(a: i128, b: i128) -> (i128, bool) {
        let mut oflow = 0;
        let r = a.subo(b, &mut oflow);
        (r, oflow != 0)
    }

    pub extern "C" fn __rust_u128_sub(a: u128, b: u128) -> u128 {
        a.sub(b)
    }

    pub extern "C" fn __rust_u128_subo(a: u128, b: u128) -> (u128, bool) {
        let mut oflow = 0;
        let r = a.subo(b, &mut oflow);
        (r, oflow != 0)
    }
}
