; ModuleID = 'freeze.c'
source_filename = "freeze.c"
target datalayout = "e-m:e-p:32:32-p270:32:32-p271:32:32-p272:64:64-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-unknown-linux-elf"

@b = dso_local local_unnamed_addr global i64 0, align 8

; Function Attrs: nofree norecurse nounwind willreturn
define dso_local i32 @c(i32 returned %a) local_unnamed_addr #0 {
entry:
  %0 = load i64, i64* @b, align 8, !tbaa !4
  %.frozen = freeze i64 %0
  %div = sdiv i64 %.frozen, 2
  %1 = mul i64 %div, 2
  %rem.decomposed = sub i64 %.frozen, %1
  %conv = sext i32 %a to i64
  %cmp = icmp eq i64 %rem.decomposed, %conv
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  store i64 %div, i64* @b, align 8, !tbaa !4
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret i32 %a
}

; Function Attrs: nofree norecurse nounwind willreturn
define dso_local i32 @main() local_unnamed_addr #0 {
entry:
  %call = call i32 @c(i32 0)
  ret i32 0
}

attributes #0 = { nofree norecurse nounwind willreturn "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}
!llvm.commandline = !{!3}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"clang version 12.0.0 (https://github.com/llvm/llvm-project/ b978a93635b584db380274d7c8963c73989944a1)"}
!3 = !{!"/home/rscott/Software/clang+llvm-12.0.0-x86_64-linux-gnu-ubuntu-20.04/bin/clang-12 -fno-discard-value-names -frecord-command-line -S -D CRUCIBLE -emit-llvm -I ../../../c-src/includes -O1 --target=i386-unknown-linux-elf freeze.c -o freeze.ll"}
!4 = !{!5, !5, i64 0}
!5 = !{!"long long", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C/C++ TBAA"}
