; ModuleID = 'T847-fail2.c'
source_filename = "T847-fail2.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: norecurse nounwind readnone uwtable willreturn
define dso_local i32 @my_abs(i32 %x) local_unnamed_addr #0 {
entry:
  %0 = call i32 @llvm.abs.i32(i32 %x, i1 true)
  ret i32 %0
}

; Function Attrs: norecurse nounwind readnone uwtable willreturn
define dso_local i32 @main() local_unnamed_addr #0 {
entry:
  %call = call i32 @my_abs(i32 -2147483648)
  ret i32 %call
}

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare i32 @llvm.abs.i32(i32, i1 immarg) #1

attributes #0 = { norecurse nounwind readnone uwtable willreturn "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nofree nosync nounwind readnone speculatable willreturn }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}
!llvm.commandline = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 12.0.0 (https://github.com/llvm/llvm-project/ b978a93635b584db380274d7c8963c73989944a1)"}
!2 = !{!"/home/rscott/Software/clang+llvm-12.0.0-x86_64-linux-gnu-ubuntu-20.04/bin/clang-12 -fno-discard-value-names -frecord-command-line -S -D CRUCIBLE -emit-llvm -I ../../../c-src/includes -O1 T847-fail2.c -o T847-fail2.ll"}
