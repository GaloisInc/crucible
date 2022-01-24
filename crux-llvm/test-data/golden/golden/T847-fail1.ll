; ModuleID = 'T847-fail1.c'
source_filename = "T847-fail1.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i64, align 8
  %z = alloca i64, align 8
  store i32 0, i32* %retval, align 4
  %call = call i32 @abs(i32 -2147483648) #2
  store i32 %call, i32* %x, align 4
  %call1 = call i64 @labs(i64 -9223372036854775808) #2
  store i64 %call1, i64* %y, align 8
  %call2 = call i64 @llabs(i64 -9223372036854775808) #2
  store i64 %call2, i64* %z, align 8
  ret i32 0
}

; Function Attrs: nounwind readnone willreturn
declare dso_local i32 @abs(i32) #1

; Function Attrs: nounwind readnone willreturn
declare dso_local i64 @labs(i64) #1

; Function Attrs: nounwind readnone willreturn
declare dso_local i64 @llabs(i64) #1

attributes #0 = { noinline nounwind optnone uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind readnone willreturn }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}
!llvm.commandline = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 12.0.0 (https://github.com/llvm/llvm-project/ b978a93635b584db380274d7c8963c73989944a1)"}
!2 = !{!"/home/rscott/Software/clang+llvm-12.0.0-x86_64-linux-gnu-ubuntu-20.04/bin/clang-12 -fno-discard-value-names -frecord-command-line -S -D CRUCIBLE -emit-llvm -I ../../../c-src/includes -O0 T847-fail1.c -o T847-fail1.ll"}
