%struct.S = type { i32, i32, [0 x i8] }

define i32 @main() {
  ; Allocate a ptr large enough to hold a %struct.S value.
  %sp = alloca %struct.S

  ; Write a %struct.S value to the pointer whose fields are all zeroes.
  ;
  ; NB: Make sure _not_ to use the empty array value `[0 x i8] []` or
  ; `[0 x i8] zeroinitializer` for the third field, because for whatever reason,
  ; Clang 20+ normalizes these to `poison` values. This, in turn, will cause
  ; the test to fail for unrelated reasons, as crucible-llvm isn't currently
  ; equipped to reason about `poison` values at this level of granularity.
  ; See #366.
  ;
  ; Luckily, Clang 20+ does _not_ normalize `[0 x i8] undef` to `poison`, and
  ; the memory model doesn't fall over when you use a zero-sized `undef` value,
  ; so we use that instead of `[]`/`zeroinitializer`. If future versions of
  ; Clang start to optimize `undef` to `poison`, then we will need to rethink
  ; how to test this.
  store %struct.S { i32 0, i32 0, [0 x i8] undef }, ptr %sp

  ; Write 0 to the second field of the struct (at offset 1).
  %sp2 = getelementptr inbounds %struct.S, ptr %sp, i32 0, i32 1
  store i32 0, ptr %sp2, align 4

  ; Load a %struct.S value from the pointer after the write above.
  %x = load %struct.S, ptr %sp, align 4

  ret i32 0
}
