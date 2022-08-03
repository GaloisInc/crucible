; ModuleID = 'test-abdpaper-32.bc'
source_filename = "test-abdpaper-32.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"x\00", align 1
@.str.1 = private unnamed_addr constant [2 x i8] c"y\00", align 1
@.str.2 = private unnamed_addr constant [2 x i8] c"z\00", align 1
@.str.3 = private unnamed_addr constant [19 x i8] c"test-abdpaper-32.c\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, i32* %1, align 4 ;%1 = 0
  %5 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0))
  store i32 %5, i32* %2, align 4 ; %2 = %5 (@crucible_int32_t "x")
  %6 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1, i64 0, i64 0))
  store i32 %6, i32* %3, align 4 ; %3 = %6 (@crucible_int32_t "y")
  %7 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  store i32 %7, i32* %4, align 4 ; %4 = %7 (@crucible_int32_t "z")
  %8 = load i32, i32* %3, align 4 ; %8 = %3
  %9 = icmp sgt i32 %8, 0         ; %8 > 0
  %10 = zext i1 %9 to i32         ; to_i32(%8)
  %11 = trunc i32 %10 to i8       ; to_i8(%10)
  call void @crucible_assume(i8 zeroext %11, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.3, i64 0, i64 0), i32 8)
  %12 = load i32, i32* %2, align 4
  %13 = load i32, i32* %3, align 4
  %14 = add nsw i32 %12, %13        ; %14 = %2 + %3
  %15 = load i32, i32* %4, align 4  ; %15 = %4
  %16 = add nsw i32 %14, %15        ; %16 = %2 + %3 + %4
  %17 = icmp sgt i32 %16, 0         ; %2 + %3 + %4 > 0
  %18 = zext i1 %17 to i32          ; to_i32 (%17)
  %19 = trunc i32 %18 to i8         ; to_i8 (%18)
  call void @crucible_assert(i8 zeroext %19, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.3, i64 0, i64 0), i32 9)
  ret i32 0
}

declare dso_local i32 @crucible_int32_t(i8*) #1

declare dso_local void @crucible_assume(i8 zeroext, i8*, i32) #1

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) #1

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 9.0.1-12 "}
