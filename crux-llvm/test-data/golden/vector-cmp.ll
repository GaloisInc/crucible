target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare void @crucible_print_uint32( i32 )


define i1 @f( i32, i32 ) {
  %v1.0 = insertelement <2 x i32> undef, i32 %0, i32 0
  %v1   = insertelement <2 x i32> %v1.0, i32 %1, i32 1

  %v2.0 = insertelement <2 x i32> undef, i32 %0, i32 1
  %v2   = insertelement <2 x i32> %v2.0, i32 %1, i32 0

  %vres = icmp ule <2 x i32> %v1, %v2

  %res0 = extractelement <2 x i1> %vres, i32 0
  %res1 = extractelement <2 x i1> %vres, i32 1

  %x    = icmp eq i1 %res0, 1
  %y    = icmp eq i1 %res1, 0
  %z    = and i1 %x, %y
  ret i1 %z
}

define i1 @g( float, float ) {
  %p = alloca <2 x float>
  %p0 = bitcast <2 x float>* %p to float*
  %p1 = getelementptr float, float* %p0, i32 1

  store float %0, float* %p0
  store float %1, float* %p1
  %v1 = load <2 x float>, <2 x float>* %p

  store float %1, float* %p0
  store float %0, float* %p1
  %v2 = load <2 x float>, <2 x float>* %p

  %vres = fcmp ole <2 x float> %v1, %v2

  %res0 = extractelement <2 x i1> %vres, i32 0
  %res1 = extractelement <2 x i1> %vres, i32 1

  %x    = icmp eq i1 %res0, 1
  %y    = icmp eq i1 %res1, 0
  %z    = and i1 %x, %y
  ret i1 %z
}

define i32 @main() {
   %fres = call i1 @f( i32 5, i32 42 )
   %fres32 = zext i1 %fres to i32

   %gres = call i1 @g( float 5.0, float 42.0 )
   %gres32 = zext i1 %gres to i32

   %x = shl i32 %gres32, 1
   %r = or i32 %fres32, %x

   call void @crucible_print_uint32( i32 %r )

   ret i32 %r
}
