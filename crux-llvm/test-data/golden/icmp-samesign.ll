; Test crucible-llvm's semantics for the `samesign` flag in `icmp` instructions.
; Specifically, the first two calls should succeed, as both arguments have the
; same signs, but the last call should return a poison value, as the arguments
; have different signs.

define i32 @main() {
  %res1 = icmp samesign eq i8 1, 1
  %res2 = icmp samesign eq i8 -1, -1
  %res3 = icmp samesign eq i8 -1, 1
  ret i32 0
}
