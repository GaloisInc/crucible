; ModuleID = 'loop_exit.bc'
source_filename = "test-data/golden/golden-loop-merging/loop_exit.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"b\00", align 1
@.str.1 = private unnamed_addr constant [49 x i8] c"test-data/golden/golden-loop-merging/loop_exit.c\00", align 1

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #0 !dbg !7 {
  call void @llvm.dbg.value(metadata i32 0, metadata !12, metadata !DIExpression()), !dbg !17
  br label %1, !dbg !18

1:                                                ; preds = %6, %0
  %2 = phi i32 [ 0, %0 ], [ %7, %6 ]
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !17
  %3 = tail call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0)) #3, !dbg !19
  call void @llvm.dbg.value(metadata i32 %3, metadata !13, metadata !DIExpression()), !dbg !20
  switch i32 %3, label %10 [
    i32 0, label %6
    i32 1, label %6
    i32 2, label %4
  ], !dbg !21

4:                                                ; preds = %1
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !17
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !17
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !17
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !17
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !17
  %5 = add nuw nsw i32 %2, 1, !dbg !22
  call void @llvm.dbg.value(metadata i32 %5, metadata !12, metadata !DIExpression()), !dbg !17
  br label %10, !dbg !26

6:                                                ; preds = %1, %1
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !17
  %7 = add nuw nsw i32 %2, 1, !dbg !27
  call void @llvm.dbg.value(metadata i32 %7, metadata !12, metadata !DIExpression()), !dbg !17
  %8 = icmp eq i32 %7, 15, !dbg !28
  br i1 %8, label %9, label %1, !dbg !18, !llvm.loop !29

9:                                                ; preds = %6
  call void @llvm.dbg.value(metadata i32 %7, metadata !12, metadata !DIExpression()), !dbg !17
  tail call void @crucible_assert(i8 zeroext 1, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.1, i64 0, i64 0), i32 18) #3, !dbg !31
  br label %10, !dbg !32

10:                                               ; preds = %1, %4, %9
  %11 = phi i32 [ 0, %9 ], [ %5, %4 ], [ %2, %1 ], !dbg !17
  ret i32 %11, !dbg !33
}

declare dso_local i32 @crucible_int32_t(i8*) local_unnamed_addr #1

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) local_unnamed_addr #1

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.value(metadata, metadata, metadata) #2

attributes #0 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind readnone speculatable }
attributes #3 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5}
!llvm.ident = !{!6}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, nameTableKind: None)
!1 = !DIFile(filename: "test-data/golden/golden-loop-merging/loop_exit.c", directory: "/home/abakst/crucible/crux-llvm")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)"}
!7 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 4, type: !8, scopeLine: 5, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !11)
!8 = !DISubroutineType(types: !9)
!9 = !{!10}
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !{!12, !13}
!12 = !DILocalVariable(name: "i", scope: !7, file: !1, line: 6, type: !10)
!13 = !DILocalVariable(name: "b", scope: !14, file: !1, line: 8, type: !10)
!14 = distinct !DILexicalBlock(scope: !15, file: !1, line: 7, column: 29)
!15 = distinct !DILexicalBlock(scope: !16, file: !1, line: 7, column: 5)
!16 = distinct !DILexicalBlock(scope: !7, file: !1, line: 7, column: 5)
!17 = !DILocation(line: 0, scope: !7)
!18 = !DILocation(line: 7, column: 5, scope: !16)
!19 = !DILocation(line: 8, column: 17, scope: !14)
!20 = !DILocation(line: 0, scope: !14)
!21 = !DILocation(line: 9, column: 13, scope: !14)
!22 = !DILocation(line: 12, column: 13, scope: !23)
!23 = distinct !DILexicalBlock(scope: !24, file: !1, line: 10, column: 15)
!24 = distinct !DILexicalBlock(scope: !25, file: !1, line: 9, column: 21)
!25 = distinct !DILexicalBlock(scope: !14, file: !1, line: 9, column: 13)
!26 = !DILocation(line: 12, column: 12, scope: !23)
!27 = !DILocation(line: 7, column: 25, scope: !15)
!28 = !DILocation(line: 7, column: 19, scope: !15)
!29 = distinct !{!29, !18, !30}
!30 = !DILocation(line: 17, column: 5, scope: !16)
!31 = !DILocation(line: 18, column: 5, scope: !7)
!32 = !DILocation(line: 20, column: 5, scope: !7)
!33 = !DILocation(line: 21, column: 1, scope: !7)
