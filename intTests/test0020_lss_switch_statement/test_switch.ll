; ModuleID = 'asdf2.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.10.0"

; Function Attrs: nounwind ssp uwtable
define zeroext i8 @test_case(i8 zeroext %in) #0 {
  %1 = alloca i8, align 1
  %2 = alloca i8, align 1
  store i8 %in, i8* %2, align 1
  %3 = load i8* %2, align 1
  %4 = zext i8 %3 to i32
  %5 = icmp eq i32 %4, 0
  br i1 %5, label %6, label %7

; <label>:6                                       ; preds = %0
  store i8 1, i8* %1
  ret i8 1

; <label>:7                                       ; preds = %0
  store i8 4, i8* %1
  ret i8 4
}

define i8 @test_case_indirect(i8 zeroext %in) #0 {
  %1 = call zeroext i8 @test_case(i8 zeroext %in)
  ret i8 %1
}

define i32 @main() #0 {
  %1 = alloca i32, align 4
  %x = alloca i8, align 1
  %ret = alloca i8, align 1
  store i32 0, i32* %1
  %2 = call zeroext i8 @lss_fresh_uint8(i8 zeroext 9)
  store i8 %2, i8* %x, align 1
  %3 = load i8* %x, align 1
  %4 = call zeroext i8 @test_case_indirect(i8 zeroext %3)
  store i8 %4, i8* %ret, align 1
  call void @lss_print_symbolic(i8* %ret)
  %5 = load i8* %ret, align 1
  %6 = zext i8 %5 to i32
  ret i32 %6
}

declare zeroext i8 @lss_fresh_uint8(i8 zeroext) #1

declare void @lss_print_symbolic(i8*) #1

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = metadata !{metadata !"Apple LLVM version 6.1.0 (clang-602.0.53) (based on LLVM 3.6.0svn)"}
