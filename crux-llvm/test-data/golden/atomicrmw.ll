@.str = private unnamed_addr constant [8 x i8] c"atomics\00"

declare void @crucible_assert(i8 noundef zeroext, i8* noundef, i32 noundef)

define i32 @atomic_xchg(i32* %ptr, i32 %val) {
  %old = atomicrmw xchg i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_add(i32* %ptr, i32 %val) {
  %old = atomicrmw add i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_sub(i32* %ptr, i32 %val) {
  %old = atomicrmw sub i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_and(i32* %ptr, i32 %val) {
  %old = atomicrmw and i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_nand(i32* %ptr, i32 %val) {
  %old = atomicrmw nand i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_or(i32* %ptr, i32 %val) {
  %old = atomicrmw or i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_xor(i32* %ptr, i32 %val) {
  %old = atomicrmw xor i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_max(i32* %ptr, i32 %val) {
  %old = atomicrmw max i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_min(i32* %ptr, i32 %val) {
  %old = atomicrmw min i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_umax(i32* %ptr, i32 %val) {
  %old = atomicrmw umax i32* %ptr, i32 %val acquire
  ret i32 %old
}

define i32 @atomic_umin(i32* %ptr, i32 %val) {
  %old = atomicrmw umin i32* %ptr, i32 %val acquire
  ret i32 %old
}

define void @test_atomic_i32_op(i32 (i32*, i32)* %atomic_op, i32 %expected_old, i32 %val, i32 %expected_new) {
  %ptr = alloca i32
  store i32 %expected_old, i32* %ptr
  %actual_old = call i32 %atomic_op(i32* %ptr, i32 %val)
  %actual_new = load i32, i32* %ptr
  %cmp_old = icmp eq i32 %expected_old, %actual_old
  %cmp_new = icmp eq i32 %expected_new, %actual_new
  %cmp_old_zext = zext i1 %cmp_old to i8
  %cmp_new_zext = zext i1 %cmp_new to i8
  %str_cast = bitcast [8 x i8]* @.str to i8*
  call void @crucible_assert(i8 noundef zeroext %cmp_old_zext, i8* noundef %str_cast, i32 noundef 0)
  call void @crucible_assert(i8 noundef zeroext %cmp_old_zext, i8* noundef %str_cast, i32 noundef 0)
  ret void
}

define i32 @main() {
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_xchg, i32 2, i32 3, i32 3)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_add,  i32 2, i32 3, i32 5)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_sub,  i32 3, i32 2, i32 1)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_and,  i32 2, i32 3, i32 2)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_nand, i32 2, i32 3, i32 4294967293)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_or,   i32 2, i32 3, i32 3)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_xor,  i32 2, i32 3, i32 1)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_max,  i32 4294967293, i32 3, i32 3)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_min,  i32 4294967293, i32 3, i32 4294967293)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_umax, i32 2, i32 3, i32 3)
  call void @test_atomic_i32_op(i32 (i32*, i32)* @atomic_umin, i32 2, i32 3, i32 2)
  ret i32 0
}
