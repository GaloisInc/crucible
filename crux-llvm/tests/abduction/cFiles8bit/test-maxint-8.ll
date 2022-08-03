; ModuleID = 'test-maxint-8.bc'
source_filename = "test-maxint-8.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"x\00", align 1
@.str.1 = private unnamed_addr constant [16 x i8] c"test-maxint-8.c\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i8, align 1
  store i32 0, i32* %1, align 4   ; %1 = 0
  %3 = call signext i8 @crucible_int8_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0))
  ;%3 = to_i32(crucible_int8_t ...)
  store i8 %3, i8* %2, align 1    ; %2 = %3
  %4 = load i8, i8* %2, align 1   ; %4 = %2
  %5 = zext i8 %4 to i32          ; %5 = to_i32 (%4)
  %6 = add nsw i32 %5, 1          ; %6 = %5 + 1
  %7 = load i8, i8* %2, align 1   ; %7 = %2
  %8 = zext i8 %7 to i32          ; %8 = to_i32 (%7)
  %9 = icmp sgt i32 %6, %8        ; %9 = %6 >s %8
  %10 = zext i1 %9 to i32         ; %10 = to_i32 (%10)
  %11 = trunc i32 %10 to i8       ; %11 = to_i8 (%10)
  call void @crucible_assert(i8 zeroext %11, i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.1, i64 0, i64 0), i32 6)
  ret i32 0
}

declare dso_local signext i8 @crucible_int8_t(i8*) #1

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) #1

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 9.0.1-12 "}
