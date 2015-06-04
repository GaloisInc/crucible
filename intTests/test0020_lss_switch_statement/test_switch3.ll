; ModuleID = 'test_switch2.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.10.0"

; Function Attrs: nounwind ssp uwtable
define void @test_case(i8 zeroext %in, i8* %out) #0 {
  %1 = alloca i8, align 1
  %2 = alloca i8*, align 8
  store i8 %in, i8* %1, align 1
  store i8* %out, i8** %2, align 8
  %3 = load i8* %1, align 1
  %4 = zext i8 %3 to i32
  switch i32 %4, label %7 [
    i32 0, label %5
  ]

; <label>:5                                       ; preds = %0
  %6 = load i8** %2, align 8
  store i8 1, i8* %6, align 1
  ret void

; <label>:7                                       ; preds = %0
  %8 = load i8** %2, align 8
  store i8 4, i8* %8, align 1
  ret void
}

; Function Attrs: nounwind ssp uwtable
define zeroext i8 @test_case_wrapper(i8 zeroext %x) #0 {
  %1 = alloca i8, align 1
  %ret = alloca i8, align 1
  store i8 %x, i8* %1, align 1
  %2 = load i8* %1, align 1
  call void @test_case(i8 zeroext %2, i8* %ret)
  %3 = load i8* %ret, align 1
  ret i8 %3
}

attributes #0 = { nounwind ssp uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = metadata !{metadata !"Apple LLVM version 6.1.0 (clang-602.0.53) (based on LLVM 3.6.0svn)"}
