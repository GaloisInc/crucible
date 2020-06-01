; ModuleID = 'charm-O2.bc'
source_filename = "../src/shrink.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare i8* @memset( i8*, i32, i64 )

; Function Attrs: nounwind uwtable
define dso_local i32 @f(i8* nocapture readonly, i8* nocapture, i64) local_unnamed_addr #0 {
  %4 = alloca <16 x i8>, align 16
  %5 = getelementptr inbounds <16 x i8>, <16 x i8>* %4, i64 0, i64 0
  call void @llvm.lifetime.start.p0i8(i64 16, i8* nonnull %5)
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull align 16 %5, i8* align 1 %0, i64 16, i1 false)
  %6 = load <16 x i8>, <16 x i8>* %4, align 16, !tbaa !2
  %7 = bitcast i8* %1 to <16 x i8>*
  store <16 x i8> %6, <16 x i8>* %7, align 1, !tbaa !2
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull align 16 %5, i8* align 1 %0, i64 %2, i1 false)
  call void @llvm.lifetime.end.p0i8(i64 16, i8* nonnull %5)
  ret i32 0
}

define i32 @main() {
  %x = alloca [16 x i8], align 16
  %x1 = bitcast [16 x i8]* %x to i8*
  %y = alloca [16 x i8], align 16
  %y1 = bitcast [16 x i8]* %y to i8*
  call i8* @memset( i8* %x1, i32 42, i64 16 );
  %r = call i32 @f( i8* %x1, i8* %y1, i64 16 )
  ret i32 %r
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #1

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i1) #1

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #1

attributes #0 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 7.1.0-svn353565-1~exp1~20190406090509.61 (branches/release_70)"}
!2 = !{!3, !3, i64 0}
!3 = !{!"omnipotent char", !4, i64 0}
!4 = !{!"Simple C/C++ TBAA"}
