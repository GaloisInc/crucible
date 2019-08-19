//! `i586` MMX instruction set.
//!
//! The intrinsics here roughly correspond to those in the `mmintrin.h` C
//! header.
//!
//! The reference is [Intel 64 and IA-32 Architectures Software Developer's
//! Manual Volume 2: Instruction Set Reference, A-Z][intel64_ref].
//!
//! [intel64_ref]: http://www.intel.de/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-instruction-set-reference-manual-325383.pdf

use crate::{
    core_arch::{simd::*, x86::*},
    mem::transmute,
};

#[cfg(test)]
use stdarch_test::assert_instr;

/// Constructs a 64-bit integer vector initialized to zero.
#[inline]
#[target_feature(enable = "mmx")]
// FIXME: this produces a movl instead of xorps on x86
// FIXME: this produces a xor intrinsic instead of xorps on x86_64
#[cfg_attr(all(test, target_arch = "x86_64"), assert_instr(xor))]
pub unsafe fn _mm_setzero_si64() -> __m64 {
    transmute(0_i64)
}

/// Adds packed 8-bit integers in `a` and `b`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddb))]
pub unsafe fn _mm_add_pi8(a: __m64, b: __m64) -> __m64 {
    paddb(a, b)
}

/// Adds packed 8-bit integers in `a` and `b`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddb))]
pub unsafe fn _m_paddb(a: __m64, b: __m64) -> __m64 {
    _mm_add_pi8(a, b)
}

/// Adds packed 16-bit integers in `a` and `b`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddw))]
pub unsafe fn _mm_add_pi16(a: __m64, b: __m64) -> __m64 {
    paddw(a, b)
}

/// Adds packed 16-bit integers in `a` and `b`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddw))]
pub unsafe fn _m_paddw(a: __m64, b: __m64) -> __m64 {
    _mm_add_pi16(a, b)
}

/// Adds packed 32-bit integers in `a` and `b`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddd))]
pub unsafe fn _mm_add_pi32(a: __m64, b: __m64) -> __m64 {
    paddd(a, b)
}

/// Adds packed 32-bit integers in `a` and `b`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddd))]
pub unsafe fn _m_paddd(a: __m64, b: __m64) -> __m64 {
    _mm_add_pi32(a, b)
}

/// Adds packed 8-bit integers in `a` and `b` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddsb))]
pub unsafe fn _mm_adds_pi8(a: __m64, b: __m64) -> __m64 {
    paddsb(a, b)
}

/// Adds packed 8-bit integers in `a` and `b` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddsb))]
pub unsafe fn _m_paddsb(a: __m64, b: __m64) -> __m64 {
    _mm_adds_pi8(a, b)
}

/// Adds packed 16-bit integers in `a` and `b` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddsw))]
pub unsafe fn _mm_adds_pi16(a: __m64, b: __m64) -> __m64 {
    paddsw(a, b)
}

/// Adds packed 16-bit integers in `a` and `b` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddsw))]
pub unsafe fn _m_paddsw(a: __m64, b: __m64) -> __m64 {
    _mm_adds_pi16(a, b)
}

/// Adds packed unsigned 8-bit integers in `a` and `b` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddusb))]
pub unsafe fn _mm_adds_pu8(a: __m64, b: __m64) -> __m64 {
    paddusb(a, b)
}

/// Adds packed unsigned 8-bit integers in `a` and `b` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddusb))]
pub unsafe fn _m_paddusb(a: __m64, b: __m64) -> __m64 {
    _mm_adds_pu8(a, b)
}

/// Adds packed unsigned 16-bit integers in `a` and `b` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddusw))]
pub unsafe fn _mm_adds_pu16(a: __m64, b: __m64) -> __m64 {
    paddusw(a, b)
}

/// Adds packed unsigned 16-bit integers in `a` and `b` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(paddusw))]
pub unsafe fn _m_paddusw(a: __m64, b: __m64) -> __m64 {
    _mm_adds_pu16(a, b)
}

/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in `a`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubb))]
pub unsafe fn _mm_sub_pi8(a: __m64, b: __m64) -> __m64 {
    psubb(a, b)
}

/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in `a`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubb))]
pub unsafe fn _m_psubb(a: __m64, b: __m64) -> __m64 {
    _mm_sub_pi8(a, b)
}

/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in `a`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubw))]
pub unsafe fn _mm_sub_pi16(a: __m64, b: __m64) -> __m64 {
    psubw(a, b)
}

/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in `a`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubw))]
pub unsafe fn _m_psubw(a: __m64, b: __m64) -> __m64 {
    _mm_sub_pi16(a, b)
}

/// Subtract packed 32-bit integers in `b` from packed 32-bit integers in `a`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubd))]
pub unsafe fn _mm_sub_pi32(a: __m64, b: __m64) -> __m64 {
    psubd(a, b)
}

/// Subtract packed 32-bit integers in `b` from packed 32-bit integers in `a`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubd))]
pub unsafe fn _m_psubd(a: __m64, b: __m64) -> __m64 {
    _mm_sub_pi32(a, b)
}

/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in `a`
/// using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubsb))]
pub unsafe fn _mm_subs_pi8(a: __m64, b: __m64) -> __m64 {
    psubsb(a, b)
}

/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in `a`
/// using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubsb))]
pub unsafe fn _m_psubsb(a: __m64, b: __m64) -> __m64 {
    _mm_subs_pi8(a, b)
}

/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in `a`
/// using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubsw))]
pub unsafe fn _mm_subs_pi16(a: __m64, b: __m64) -> __m64 {
    psubsw(a, b)
}

/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in `a`
/// using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubsw))]
pub unsafe fn _m_psubsw(a: __m64, b: __m64) -> __m64 {
    _mm_subs_pi16(a, b)
}

/// Subtract packed unsigned 8-bit integers in `b` from packed unsigned 8-bit
/// integers in `a` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubusb))]
pub unsafe fn _mm_subs_pu8(a: __m64, b: __m64) -> __m64 {
    psubusb(a, b)
}

/// Subtract packed unsigned 8-bit integers in `b` from packed unsigned 8-bit
/// integers in `a` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubusb))]
pub unsafe fn _m_psubusb(a: __m64, b: __m64) -> __m64 {
    _mm_subs_pu8(a, b)
}

/// Subtract packed unsigned 16-bit integers in `b` from packed unsigned
/// 16-bit integers in `a` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubusw))]
pub unsafe fn _mm_subs_pu16(a: __m64, b: __m64) -> __m64 {
    psubusw(a, b)
}

/// Subtract packed unsigned 16-bit integers in `b` from packed unsigned
/// 16-bit integers in `a` using saturation.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(psubusw))]
pub unsafe fn _m_psubusw(a: __m64, b: __m64) -> __m64 {
    _mm_subs_pu16(a, b)
}

/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using signed saturation.
///
/// Positive values greater than 0x7F are saturated to 0x7F. Negative values
/// less than 0x80 are saturated to 0x80.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(packsswb))]
pub unsafe fn _mm_packs_pi16(a: __m64, b: __m64) -> __m64 {
    packsswb(a, b)
}

/// Converts packed 32-bit integers from `a` and `b` to packed 16-bit integers
/// using signed saturation.
///
/// Positive values greater than 0x7F are saturated to 0x7F. Negative values
/// less than 0x80 are saturated to 0x80.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(packssdw))]
pub unsafe fn _mm_packs_pi32(a: __m64, b: __m64) -> __m64 {
    packssdw(a, b)
}

/// Compares whether each element of `a` is greater than the corresponding
/// element of `b` returning `0` for `false` and `-1` for `true`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(pcmpgtb))]
pub unsafe fn _mm_cmpgt_pi8(a: __m64, b: __m64) -> __m64 {
    pcmpgtb(a, b)
}

/// Compares whether each element of `a` is greater than the corresponding
/// element of `b` returning `0` for `false` and `-1` for `true`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(pcmpgtw))]
pub unsafe fn _mm_cmpgt_pi16(a: __m64, b: __m64) -> __m64 {
    pcmpgtw(a, b)
}

/// Compares whether each element of `a` is greater than the corresponding
/// element of `b` returning `0` for `false` and `-1` for `true`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(pcmpgtd))]
pub unsafe fn _mm_cmpgt_pi32(a: __m64, b: __m64) -> __m64 {
    pcmpgtd(a, b)
}

/// Unpacks the upper two elements from two `i16x4` vectors and interleaves
/// them into the result: `[a.2, b.2, a.3, b.3]`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(punpckhwd))] // FIXME punpcklbw expected
pub unsafe fn _mm_unpackhi_pi16(a: __m64, b: __m64) -> __m64 {
    punpckhwd(a, b)
}

/// Unpacks the upper four elements from two `i8x8` vectors and interleaves
/// them into the result: `[a.4, b.4, a.5, b.5, a.6, b.6, a.7, b.7]`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(punpckhbw))]
pub unsafe fn _mm_unpackhi_pi8(a: __m64, b: __m64) -> __m64 {
    punpckhbw(a, b)
}

/// Unpacks the lower four elements from two `i8x8` vectors and interleaves
/// them into the result: `[a.0, b.0, a.1, b.1, a.2, b.2, a.3, b.3]`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(punpcklbw))]
pub unsafe fn _mm_unpacklo_pi8(a: __m64, b: __m64) -> __m64 {
    punpcklbw(a, b)
}

/// Unpacks the lower two elements from two `i16x4` vectors and interleaves
/// them into the result: `[a.0 b.0 a.1 b.1]`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(punpcklwd))]
pub unsafe fn _mm_unpacklo_pi16(a: __m64, b: __m64) -> __m64 {
    punpcklwd(a, b)
}

/// Unpacks the upper element from two `i32x2` vectors and interleaves them
/// into the result: `[a.1, b.1]`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(punpckhdq))]
pub unsafe fn _mm_unpackhi_pi32(a: __m64, b: __m64) -> __m64 {
    punpckhdq(a, b)
}

/// Unpacks the lower element from two `i32x2` vectors and interleaves them
/// into the result: `[a.0, b.0]`.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(punpckldq))]
pub unsafe fn _mm_unpacklo_pi32(a: __m64, b: __m64) -> __m64 {
    punpckldq(a, b)
}

/// Sets packed 16-bit integers in dst with the supplied values.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_set_pi16(e3: i16, e2: i16, e1: i16, e0: i16) -> __m64 {
    _mm_setr_pi16(e0, e1, e2, e3)
}

/// Sets packed 32-bit integers in dst with the supplied values.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_set_pi32(e1: i32, e0: i32) -> __m64 {
    _mm_setr_pi32(e0, e1)
}

/// Sets packed 8-bit integers in dst with the supplied values.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_set_pi8(e7: i8, e6: i8, e5: i8, e4: i8, e3: i8, e2: i8, e1: i8, e0: i8) -> __m64 {
    _mm_setr_pi8(e0, e1, e2, e3, e4, e5, e6, e7)
}

/// Broadcasts 16-bit integer a to all all elements of dst.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_set1_pi16(a: i16) -> __m64 {
    _mm_setr_pi16(a, a, a, a)
}

/// Broadcasts 32-bit integer a to all all elements of dst.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_set1_pi32(a: i32) -> __m64 {
    _mm_setr_pi32(a, a)
}

/// Broadcasts 8-bit integer a to all all elements of dst.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_set1_pi8(a: i8) -> __m64 {
    _mm_setr_pi8(a, a, a, a, a, a, a, a)
}

/// Sets packed 16-bit integers in dst with the supplied values in reverse
/// order.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_setr_pi16(e0: i16, e1: i16, e2: i16, e3: i16) -> __m64 {
    transmute(i16x4::new(e0, e1, e2, e3))
}

/// Sets packed 32-bit integers in dst with the supplied values in reverse
/// order.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_setr_pi32(e0: i32, e1: i32) -> __m64 {
    transmute(i32x2::new(e0, e1))
}

/// Sets packed 8-bit integers in dst with the supplied values in reverse order.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_setr_pi8(
    e0: i8,
    e1: i8,
    e2: i8,
    e3: i8,
    e4: i8,
    e5: i8,
    e6: i8,
    e7: i8,
) -> __m64 {
    transmute(i8x8::new(e0, e1, e2, e3, e4, e5, e6, e7))
}

/// Empty the MMX state, which marks the x87 FPU registers as available for use
/// by x87 instructions. This instruction must be used at the end of all MMX
/// technology procedures.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(emms))]
pub unsafe fn _mm_empty() {
    emms()
}

/// Empty the MMX state, which marks the x87 FPU registers as available for use
/// by x87 instructions. This instruction must be used at the end of all MMX
/// technology procedures.
#[inline]
#[target_feature(enable = "mmx")]
#[cfg_attr(test, assert_instr(emms))]
pub unsafe fn _m_empty() {
    emms()
}

/// Copies 32-bit integer `a` to the lower elements of the return value, and zero
/// the upper element of the return value.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_cvtsi32_si64(a: i32) -> __m64 {
    transmute(i32x2::new(a, 0))
}

/// Return the lower 32-bit integer in `a`.
#[inline]
#[target_feature(enable = "mmx")]
pub unsafe fn _mm_cvtsi64_si32(a: __m64) -> i32 {
    let r: i32x2 = transmute(a);
    r.0
}

#[allow(improper_ctypes)]
extern "C" {
    #[link_name = "llvm.x86.mmx.padd.b"]
    fn paddb(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.padd.w"]
    fn paddw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.padd.d"]
    fn paddd(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.padds.b"]
    fn paddsb(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.padds.w"]
    fn paddsw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.paddus.b"]
    fn paddusb(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.paddus.w"]
    fn paddusw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.psub.b"]
    fn psubb(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.psub.w"]
    fn psubw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.psub.d"]
    fn psubd(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.psubs.b"]
    fn psubsb(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.psubs.w"]
    fn psubsw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.psubus.b"]
    fn psubusb(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.psubus.w"]
    fn psubusw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.packsswb"]
    fn packsswb(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.packssdw"]
    fn packssdw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.pcmpgt.b"]
    fn pcmpgtb(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.pcmpgt.w"]
    fn pcmpgtw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.pcmpgt.d"]
    fn pcmpgtd(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.punpckhwd"]
    fn punpckhwd(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.punpcklwd"]
    fn punpcklwd(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.punpckhbw"]
    fn punpckhbw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.punpcklbw"]
    fn punpcklbw(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.punpckhdq"]
    fn punpckhdq(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.punpckldq"]
    fn punpckldq(a: __m64, b: __m64) -> __m64;
    #[link_name = "llvm.x86.mmx.emms"]
    fn emms();
}

#[cfg(test)]
mod tests {
    use crate::core_arch::x86::*;
    use stdarch_test::simd_test;

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_setzero_si64() {
        let r: __m64 = transmute(0_i64);
        assert_eq_m64(r, _mm_setzero_si64());
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_add_pi8() {
        let a = _mm_setr_pi8(-1, -1, 1, 1, -1, 0, 1, 0);
        let b = _mm_setr_pi8(-127, 101, 99, 126, 0, -1, 0, 1);
        let e = _mm_setr_pi8(-128, 100, 100, 127, -1, -1, 1, 1);
        assert_eq_m64(e, _mm_add_pi8(a, b));
        assert_eq_m64(e, _m_paddb(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_add_pi16() {
        let a = _mm_setr_pi16(-1, -1, 1, 1);
        let b = _mm_setr_pi16(i16::min_value() + 1, 30001, -30001, i16::max_value() - 1);
        let e = _mm_setr_pi16(i16::min_value(), 30000, -30000, i16::max_value());
        assert_eq_m64(e, _mm_add_pi16(a, b));
        assert_eq_m64(e, _m_paddw(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_add_pi32() {
        let a = _mm_setr_pi32(1, -1);
        let b = _mm_setr_pi32(i32::max_value() - 1, i32::min_value() + 1);
        let e = _mm_setr_pi32(i32::max_value(), i32::min_value());
        assert_eq_m64(e, _mm_add_pi32(a, b));
        assert_eq_m64(e, _m_paddd(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_adds_pi8() {
        let a = _mm_setr_pi8(-100, -1, 1, 100, -1, 0, 1, 0);
        let b = _mm_setr_pi8(-100, 1, -1, 100, 0, -1, 0, 1);
        let e = _mm_setr_pi8(i8::min_value(), 0, 0, i8::max_value(), -1, -1, 1, 1);
        assert_eq_m64(e, _mm_adds_pi8(a, b));
        assert_eq_m64(e, _m_paddsb(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_adds_pi16() {
        let a = _mm_setr_pi16(-32000, 32000, 4, 0);
        let b = _mm_setr_pi16(-32000, 32000, -5, 1);
        let e = _mm_setr_pi16(i16::min_value(), i16::max_value(), -1, 1);
        assert_eq_m64(e, _mm_adds_pi16(a, b));
        assert_eq_m64(e, _m_paddsw(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_adds_pu8() {
        let a = _mm_setr_pi8(0, 1, 2, 3, 4, 5, 6, 200u8 as i8);
        let b = _mm_setr_pi8(0, 10, 20, 30, 40, 50, 60, 200u8 as i8);
        let e = _mm_setr_pi8(0, 11, 22, 33, 44, 55, 66, u8::max_value() as i8);
        assert_eq_m64(e, _mm_adds_pu8(a, b));
        assert_eq_m64(e, _m_paddusb(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_adds_pu16() {
        let a = _mm_setr_pi16(0, 1, 2, 60000u16 as i16);
        let b = _mm_setr_pi16(0, 10, 20, 60000u16 as i16);
        let e = _mm_setr_pi16(0, 11, 22, u16::max_value() as i16);
        assert_eq_m64(e, _mm_adds_pu16(a, b));
        assert_eq_m64(e, _m_paddusw(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_sub_pi8() {
        let a = _mm_setr_pi8(0, 0, 1, 1, -1, -1, 0, 0);
        let b = _mm_setr_pi8(-1, 1, -2, 2, 100, -100, -127, 127);
        let e = _mm_setr_pi8(1, -1, 3, -1, -101, 99, 127, -127);
        assert_eq_m64(e, _mm_sub_pi8(a, b));
        assert_eq_m64(e, _m_psubb(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_sub_pi16() {
        let a = _mm_setr_pi16(-20000, -20000, 20000, 30000);
        let b = _mm_setr_pi16(-10000, 10000, -10000, 30000);
        let e = _mm_setr_pi16(-10000, -30000, 30000, 0);
        assert_eq_m64(e, _mm_sub_pi16(a, b));
        assert_eq_m64(e, _m_psubw(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_sub_pi32() {
        let a = _mm_setr_pi32(500_000, -500_000);
        let b = _mm_setr_pi32(500_000, 500_000);
        let e = _mm_setr_pi32(0, -1_000_000);
        assert_eq_m64(e, _mm_sub_pi32(a, b));
        assert_eq_m64(e, _m_psubd(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_subs_pi8() {
        let a = _mm_setr_pi8(-100, 100, 0, 0, 0, 0, -5, 5);
        let b = _mm_setr_pi8(100, -100, i8::min_value(), 127, -1, 1, 3, -3);
        let e = _mm_setr_pi8(
            i8::min_value(),
            i8::max_value(),
            i8::max_value(),
            -127,
            1,
            -1,
            -8,
            8,
        );
        assert_eq_m64(e, _mm_subs_pi8(a, b));
        assert_eq_m64(e, _m_psubsb(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_subs_pi16() {
        let a = _mm_setr_pi16(-20000, 20000, 0, 0);
        let b = _mm_setr_pi16(20000, -20000, -1, 1);
        let e = _mm_setr_pi16(i16::min_value(), i16::max_value(), 1, -1);
        assert_eq_m64(e, _mm_subs_pi16(a, b));
        assert_eq_m64(e, _m_psubsw(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_subs_pu8() {
        let a = _mm_setr_pi8(50, 10, 20, 30, 40, 60, 70, 80);
        let b = _mm_setr_pi8(60, 20, 30, 40, 30, 20, 10, 0);
        let e = _mm_setr_pi8(0, 0, 0, 0, 10, 40, 60, 80);
        assert_eq_m64(e, _mm_subs_pu8(a, b));
        assert_eq_m64(e, _m_psubusb(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_subs_pu16() {
        let a = _mm_setr_pi16(10000, 200, 0, 44444u16 as i16);
        let b = _mm_setr_pi16(20000, 300, 1, 11111);
        let e = _mm_setr_pi16(0, 0, 0, 33333u16 as i16);
        assert_eq_m64(e, _mm_subs_pu16(a, b));
        assert_eq_m64(e, _m_psubusw(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_packs_pi16() {
        let a = _mm_setr_pi16(-1, 2, -3, 4);
        let b = _mm_setr_pi16(-5, 6, -7, 8);
        let r = _mm_setr_pi8(-1, 2, -3, 4, -5, 6, -7, 8);
        assert_eq_m64(r, _mm_packs_pi16(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_packs_pi32() {
        let a = _mm_setr_pi32(-1, 2);
        let b = _mm_setr_pi32(-5, 6);
        let r = _mm_setr_pi16(-1, 2, -5, 6);
        assert_eq_m64(r, _mm_packs_pi32(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_cmpgt_pi8() {
        let a = _mm_setr_pi8(0, 1, 2, 3, 4, 5, 6, 7);
        let b = _mm_setr_pi8(8, 7, 6, 5, 4, 3, 2, 1);
        let r = _mm_setr_pi8(0, 0, 0, 0, 0, -1, -1, -1);
        assert_eq_m64(r, _mm_cmpgt_pi8(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_cmpgt_pi16() {
        let a = _mm_setr_pi16(0, 1, 2, 3);
        let b = _mm_setr_pi16(4, 3, 2, 1);
        let r = _mm_setr_pi16(0, 0, 0, -1);
        assert_eq_m64(r, _mm_cmpgt_pi16(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_cmpgt_pi32() {
        let a = _mm_setr_pi32(0, 3);
        let b = _mm_setr_pi32(1, 2);
        let r0 = _mm_setr_pi32(0, -1);
        let r1 = _mm_setr_pi32(-1, 0);

        assert_eq_m64(r0, _mm_cmpgt_pi32(a, b));
        assert_eq_m64(r1, _mm_cmpgt_pi32(b, a));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_unpackhi_pi8() {
        let a = _mm_setr_pi8(0, 3, 4, 7, 8, 11, 12, 15);
        let b = _mm_setr_pi8(1, 2, 5, 6, 9, 10, 13, 14);
        let r = _mm_setr_pi8(8, 9, 11, 10, 12, 13, 15, 14);

        assert_eq_m64(r, _mm_unpackhi_pi8(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_unpacklo_pi8() {
        let a = _mm_setr_pi8(0, 1, 2, 3, 4, 5, 6, 7);
        let b = _mm_setr_pi8(8, 9, 10, 11, 12, 13, 14, 15);
        let r = _mm_setr_pi8(0, 8, 1, 9, 2, 10, 3, 11);
        assert_eq_m64(r, _mm_unpacklo_pi8(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_unpackhi_pi16() {
        let a = _mm_setr_pi16(0, 1, 2, 3);
        let b = _mm_setr_pi16(4, 5, 6, 7);
        let r = _mm_setr_pi16(2, 6, 3, 7);
        assert_eq_m64(r, _mm_unpackhi_pi16(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_unpacklo_pi16() {
        let a = _mm_setr_pi16(0, 1, 2, 3);
        let b = _mm_setr_pi16(4, 5, 6, 7);
        let r = _mm_setr_pi16(0, 4, 1, 5);
        assert_eq_m64(r, _mm_unpacklo_pi16(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_unpackhi_pi32() {
        let a = _mm_setr_pi32(0, 3);
        let b = _mm_setr_pi32(1, 2);
        let r = _mm_setr_pi32(3, 2);

        assert_eq_m64(r, _mm_unpackhi_pi32(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_unpacklo_pi32() {
        let a = _mm_setr_pi32(0, 3);
        let b = _mm_setr_pi32(1, 2);
        let r = _mm_setr_pi32(0, 1);

        assert_eq_m64(r, _mm_unpacklo_pi32(a, b));
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_empty() {
        _mm_empty();
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_m_empty() {
        _m_empty();
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_cvtsi32_si64() {
        let a = _mm_cvtsi32_si64(42);
        let b = _mm_setr_pi32(42, 0);
        assert_eq_m64(a, b);
    }

    #[simd_test(enable = "mmx")]
    unsafe fn test_mm_cvtsi64_si32() {
        let a = _mm_setr_pi32(42, 666);
        let b = _mm_cvtsi64_si32(a);
        assert_eq!(b, 42);
    }
}
