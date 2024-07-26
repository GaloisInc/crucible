@.str = private unnamed_addr constant [8 x i8] c"atomics\00"

declare void @crucible_assert(i8 noundef zeroext, i8* noundef, i32 noundef)

define float @atomic_fmax(float* %ptr, float %val) {
  %old = atomicrmw fmax float* %ptr, float %val acquire
  ret float %old
}

define float @atomic_fmin(float* %ptr, float %val) {
  %old = atomicrmw fmin float* %ptr, float %val acquire
  ret float %old
}

define void @test_atomic_float_op(float (float*, float)* %atomic_op, float %expected_old, float %val, float %expected_new) {
  %ptr = alloca float
  store float %expected_old, float* %ptr
  %actual_old = call float %atomic_op(float* %ptr, float %val)
  %actual_new = load float, float* %ptr
  %cmp_old = fcmp oeq float %expected_old, %actual_old
  %cmp_new = fcmp oeq float %expected_new, %actual_new
  %cmp_old_zext = zext i1 %cmp_old to i8
  %cmp_new_zext = zext i1 %cmp_new to i8
  %str_cast = bitcast [8 x i8]* @.str to i8*
  call void @crucible_assert(i8 noundef zeroext %cmp_old_zext, i8* noundef %str_cast, i32 noundef 0)
  call void @crucible_assert(i8 noundef zeroext %cmp_old_zext, i8* noundef %str_cast, i32 noundef 0)
  ret void
}

define i32 @main() {
  call void @test_atomic_float_op(float (float*, float)* @atomic_fmax, float 2.5, float 3.0, float 3.0)
  call void @test_atomic_float_op(float (float*, float)* @atomic_fmin, float 2.5, float 3.0, float 2.5)
  ret i32 0
}
