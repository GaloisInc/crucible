; Check that crucible-llvm can reckon with a "temporary" `poison` value that
; only exists in a vector constant before being overwritten by an
; `insertelement` instruction.
;
; In general, crucible-llvm's support for reasoning about `poison` is quite
; limited (see #366), but on the other hand, Clang does actually produce LLVM
; bitcode code that looks like what is seen below if you enable optimizations.
; In particular, the code in the T1177.c test case is optimized to something
; resembling the code below as a result of Clang's InstCombine pass with later
; LLVM versions.
;
; We have minimized the `poison`-related parts of the T1177.c test case into the
; code below, which we include as its own test case. While T1177.c does test
; similar code, the presence or absence of `poison` is highly dependent on the
; LLVM version, so we include this as a separate test to ensure that this code
; pattern is tested more broadly.

define i32 @main() {
  %v = insertelement <2 x i32> <i32 poison, i32 1>, i32 0, i64 0
  %r = extractelement <2 x i32> %v, i32 0
  ret i32 %r
}
