; ModuleID = 'T847-succeed.c'
source_filename = "T847-succeed.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"x\00", align 1
@.str.1 = private unnamed_addr constant [2 x i8] c"z\00", align 1
@.str.2 = private unnamed_addr constant [15 x i8] c"T847-succeed.c\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @abs_spec(i32 %x) #0 {
entry:
  %retval = alloca i32, align 4
  %x.addr = alloca i32, align 4
  store i32 %x, i32* %x.addr, align 4
  %0 = load i32, i32* %x.addr, align 4
  %cmp = icmp slt i32 %0, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %1 = load i32, i32* %x.addr, align 4
  %sub = sub nsw i32 0, %1
  store i32 %sub, i32* %retval, align 4
  br label %return

if.else:                                          ; preds = %entry
  %2 = load i32, i32* %x.addr, align 4
  store i32 %2, i32* %retval, align 4
  br label %return

return:                                           ; preds = %if.else, %if.then
  %3 = load i32, i32* %retval, align 4
  ret i32 %3
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i64 @labs_spec(i64 %x) #0 {
entry:
  %retval = alloca i64, align 8
  %x.addr = alloca i64, align 8
  store i64 %x, i64* %x.addr, align 8
  %0 = load i64, i64* %x.addr, align 8
  %cmp = icmp slt i64 %0, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %1 = load i64, i64* %x.addr, align 8
  %sub = sub nsw i64 0, %1
  store i64 %sub, i64* %retval, align 8
  br label %return

if.else:                                          ; preds = %entry
  %2 = load i64, i64* %x.addr, align 8
  store i64 %2, i64* %retval, align 8
  br label %return

return:                                           ; preds = %if.else, %if.then
  %3 = load i64, i64* %retval, align 8
  ret i64 %3
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i64 @llabs_spec(i64 %x) #0 {
entry:
  %retval = alloca i64, align 8
  %x.addr = alloca i64, align 8
  store i64 %x, i64* %x.addr, align 8
  %0 = load i64, i64* %x.addr, align 8
  %cmp = icmp slt i64 %0, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %1 = load i64, i64* %x.addr, align 8
  %sub = sub nsw i64 0, %1
  store i64 %sub, i64* %retval, align 8
  br label %return

if.else:                                          ; preds = %entry
  %2 = load i64, i64* %x.addr, align 8
  store i64 %2, i64* %retval, align 8
  br label %return

return:                                           ; preds = %if.else, %if.then
  %3 = load i64, i64* %retval, align 8
  ret i64 %3
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i64, align 8
  %z = alloca i64, align 8
  store i32 0, i32* %retval, align 4
  %call = call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0))
  store i32 %call, i32* %x, align 4
  %call1 = call i64 (...) @__VERIFIER_nondet_long()
  store i64 %call1, i64* %y, align 8
  %call2 = call i64 @crucible_int64_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1, i64 0, i64 0))
  store i64 %call2, i64* %z, align 8
  %0 = load i32, i32* %x, align 4
  %cmp = icmp ne i32 %0, -2147483648
  %conv = zext i1 %cmp to i32
  %conv3 = trunc i32 %conv to i8
  call void @crucible_assume(i8 zeroext %conv3, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.2, i64 0, i64 0), i32 35)
  %1 = load i64, i64* %y, align 8
  %cmp4 = icmp ne i64 %1, -9223372036854775808
  %conv5 = zext i1 %cmp4 to i32
  %conv6 = trunc i32 %conv5 to i8
  call void @crucible_assume(i8 zeroext %conv6, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.2, i64 0, i64 0), i32 36)
  %2 = load i64, i64* %z, align 8
  %cmp7 = icmp ne i64 %2, -9223372036854775808
  %conv8 = zext i1 %cmp7 to i32
  %conv9 = trunc i32 %conv8 to i8
  call void @crucible_assume(i8 zeroext %conv9, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.2, i64 0, i64 0), i32 37)
  %3 = load i32, i32* %x, align 4
  %call10 = call i32 @abs(i32 %3) #3
  %4 = load i32, i32* %x, align 4
  %call11 = call i32 @abs_spec(i32 %4)
  %cmp12 = icmp eq i32 %call10, %call11
  %conv13 = zext i1 %cmp12 to i32
  %conv14 = trunc i32 %conv13 to i8
  call void @crucible_assert(i8 zeroext %conv14, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.2, i64 0, i64 0), i32 39)
  %5 = load i64, i64* %y, align 8
  %call15 = call i64 @labs(i64 %5) #3
  %6 = load i64, i64* %y, align 8
  %call16 = call i64 @labs_spec(i64 %6)
  %cmp17 = icmp eq i64 %call15, %call16
  %conv18 = zext i1 %cmp17 to i32
  %conv19 = trunc i32 %conv18 to i8
  call void @crucible_assert(i8 zeroext %conv19, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.2, i64 0, i64 0), i32 40)
  %7 = load i64, i64* %z, align 8
  %call20 = call i64 @llabs(i64 %7) #3
  %8 = load i64, i64* %z, align 8
  %call21 = call i64 @llabs_spec(i64 %8)
  %cmp22 = icmp eq i64 %call20, %call21
  %conv23 = zext i1 %cmp22 to i32
  %conv24 = trunc i32 %conv23 to i8
  call void @crucible_assert(i8 zeroext %conv24, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.2, i64 0, i64 0), i32 41)

  ;;;;;
  ;; START OF MANUALLY EDITED BITCODE
  ;;;;;

  %call.llvm.abs = call i32 @llvm.abs.i32(i32 -2147483648, i1 false)
  %cmp.llvm.abs = icmp eq i32 %call.llvm.abs, -2147483648
  %conv.llvm.abs = zext i1 %cmp.llvm.abs to i8
  call void @crucible_assert(i8 zeroext %conv.llvm.abs, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.2, i64 0, i64 0), i32 41)

  ;;;;;
  ;; END OF MANUALLY EDITED BITCODE
  ;;;;;

  ret i32 0
}

declare dso_local i32 @crucible_int32_t(i8*) #1

declare dso_local i64 @__VERIFIER_nondet_long(...) #1

declare dso_local i64 @crucible_int64_t(i8*) #1

declare dso_local void @crucible_assume(i8 zeroext, i8*, i32) #1

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) #1

; Function Attrs: nounwind readnone willreturn
declare dso_local i32 @abs(i32) #2

; Function Attrs: nounwind readnone willreturn
declare dso_local i64 @labs(i64) #2

; Function Attrs: nounwind readnone willreturn
declare dso_local i64 @llabs(i64) #2

;;;;;
;; START OF MANUALLY EDITED BITCODE
;;;;;

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare i32 @llvm.abs.i32(i32, i1 immarg) #1

;;;;;
;; END OF MANUALLY EDITED BITCODE
;;;;;

attributes #0 = { noinline nounwind optnone uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind readnone willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind readnone willreturn }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}
!llvm.commandline = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 12.0.0 (https://github.com/llvm/llvm-project/ b978a93635b584db380274d7c8963c73989944a1)"}
!2 = !{!"/home/rscott/Software/clang+llvm-12.0.0-x86_64-linux-gnu-ubuntu-20.04/bin/clang-12 -fno-discard-value-names -frecord-command-line -S -D CRUCIBLE -emit-llvm -I ../../../c-src/includes -O0 T847-succeed.c -o T847-succeed.ll"}
