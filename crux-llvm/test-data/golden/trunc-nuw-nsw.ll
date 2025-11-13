; Test crucible-llvm's semantics for the `nuw`/`nsw` flags in `trunc`
; instructions.

define i32 @main() {
  ; These should succeed, as no overflow is involved.
  %res1 = trunc nuw i16 0 to i8
  %res2 = trunc nsw i16 1 to i8

  ; This should fail, as `i16 u0xffff` is truncated to `i8 u0xff`, and if this
  ; were zero-extended back to an `i16`, you would get `u0x00ff`, which is not
  ; equal to the original value.
  %res3 = trunc nuw i16 u0xffff to i8

  ; This should fail, as `i16 u0x00ff` is truncated to `i8 u0xff`, and if this
  ; were sign-extended back to an `i16`, you would get `u0xffff`, which is not
  ; equal to the original value.
  %res4 = trunc nsw i16 u0x00ff to i8

  ret i32 0
}
