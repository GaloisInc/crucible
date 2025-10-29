; Test crucible-llvm's semantics for the `nneg` flag in `zext` instructions.
; Specifically, the first call (with a non-negative argument) should succeed,
; but the second call (with a negative argument) should return a poison value.

define i32 @main() {
  %res1 = zext nneg i32 1 to i64
  %res2 = zext nneg i32 -1 to i64
  ret i32 0
}
