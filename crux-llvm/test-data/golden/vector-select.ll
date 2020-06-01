target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare void @crucible_print_uint32( i32 )


define i1 @f( i1, i1 ) {
  %v1.0 = insertelement <2 x i32> undef, i32 42, i32 0
  %v1   = insertelement <2 x i32> %v1.0, i32 43, i32 1

  %v2.0 = insertelement <2 x i32> undef, i32 44, i32 0
  %v2   = insertelement <2 x i32> %v2.0, i32 45, i32 1

  %c.0  = insertelement <2 x i1> undef, i1 %0, i32 0
  %c    = insertelement <2 x i1> %c.0,  i1 %1, i32 1

  %vres = select <2 x i1> %c, <2 x i32> %v1, <2 x i32> %v2

  %res0 = extractelement <2 x i32> %vres, i32 0
  %res1 = extractelement <2 x i32> %vres, i32 1

  %x    = icmp eq i32 %res0, 44
  %y    = icmp eq i32 %res1, 43
  %z    = and i1 %x, %y
  ret i1 %z
}

define i32 @main() {
   %res = call i1 @f( i1 0, i1 1 )
   %res32 = zext i1 %res to i32

   call void @crucible_print_uint32( i32 %res32 )

   ret i32 %res32
}
