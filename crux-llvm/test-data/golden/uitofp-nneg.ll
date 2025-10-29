; Test crucible-llvm's semantics for the `nneg` flag in `uitofp` instructions.
; Specifically, the first call (with a non-negative argument) should succeed,
; but the second call (with a negative argument) should return a poison value.

define i32 @main() {
  %res1 = uitofp nneg i32 1 to float
  %res2 = uitofp nneg i32 -1 to float
  ret i32 0
}
