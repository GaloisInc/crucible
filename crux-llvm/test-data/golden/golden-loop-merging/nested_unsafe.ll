; ModuleID = 'nested_unsafe.bc'
source_filename = "test-data/golden/golden-loop-merging/nested_unsafe.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"b\00", align 1
@.str.1 = private unnamed_addr constant [53 x i8] c"test-data/golden/golden-loop-merging/nested_unsafe.c\00", align 1

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #0 !dbg !7 {
  call void @llvm.dbg.value(metadata i32 1, metadata !12, metadata !DIExpression()), !dbg !22
  br label %1, !dbg !23

1:                                                ; preds = %0, %14
  %2 = phi i32 [ 1, %0 ], [ %16, %14 ]
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 1, metadata !17, metadata !DIExpression()), !dbg !24
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !22
  %3 = icmp slt i32 %2, 1, !dbg !25
  br i1 %3, label %14, label %4, !dbg !26

4:                                                ; preds = %1, %10
  %5 = phi i32 [ %12, %10 ], [ 1, %1 ]
  %6 = phi i32 [ %11, %10 ], [ %2, %1 ]
  call void @llvm.dbg.value(metadata i32 %5, metadata !17, metadata !DIExpression()), !dbg !24
  call void @llvm.dbg.value(metadata i32 %6, metadata !12, metadata !DIExpression()), !dbg !22
  %7 = tail call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0)) #3, !dbg !27
  call void @llvm.dbg.value(metadata i32 %7, metadata !19, metadata !DIExpression()), !dbg !28
  switch i32 %7, label %21 [
    i32 1, label %10
    i32 2, label %8
  ], !dbg !29

8:                                                ; preds = %4
  %9 = add nsw i32 %6, 1, !dbg !30
  call void @llvm.dbg.value(metadata i32 %9, metadata !12, metadata !DIExpression()), !dbg !22
  br label %10, !dbg !32

10:                                               ; preds = %4, %8
  %11 = phi i32 [ %9, %8 ], [ %6, %4 ], !dbg !33
  %12 = add nuw i32 %5, 1, !dbg !34
  call void @llvm.dbg.value(metadata i32 %12, metadata !17, metadata !DIExpression()), !dbg !24
  call void @llvm.dbg.value(metadata i32 %11, metadata !12, metadata !DIExpression()), !dbg !22
  %13 = icmp eq i32 %5, %2, !dbg !25
  br i1 %13, label %14, label %4, !dbg !26, !llvm.loop !35

14:                                               ; preds = %10, %1
  %15 = phi i32 [ %2, %1 ], [ %11, %10 ], !dbg !37
  call void @llvm.dbg.value(metadata i32 %15, metadata !12, metadata !DIExpression()), !dbg !22
  %16 = add nsw i32 %15, 1, !dbg !38
  call void @llvm.dbg.value(metadata i32 %16, metadata !12, metadata !DIExpression()), !dbg !22
  %17 = icmp slt i32 %16, 9, !dbg !39
  br i1 %17, label %1, label %18, !dbg !23, !llvm.loop !40

18:                                               ; preds = %14
  call void @llvm.dbg.value(metadata i32 %16, metadata !12, metadata !DIExpression()), !dbg !22
  %19 = icmp slt i32 %16, 17, !dbg !42
  %20 = zext i1 %19 to i8, !dbg !43
  tail call void @crucible_assert(i8 zeroext %20, i8* getelementptr inbounds ([53 x i8], [53 x i8]* @.str.1, i64 0, i64 0), i32 19) #3, !dbg !44
  br label %21, !dbg !45

21:                                               ; preds = %4, %18
  ret i32 0, !dbg !46
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
!1 = !DIFile(filename: "test-data/golden/golden-loop-merging/nested_unsafe.c", directory: "/home/abakst/crucible/crux-llvm")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)"}
!7 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 4, type: !8, scopeLine: 5, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !11)
!8 = !DISubroutineType(types: !9)
!9 = !{!10}
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !{!12, !13, !17, !19}
!12 = !DILocalVariable(name: "i", scope: !7, file: !1, line: 6, type: !10)
!13 = !DILocalVariable(name: "i0", scope: !14, file: !1, line: 8, type: !10)
!14 = distinct !DILexicalBlock(scope: !15, file: !1, line: 7, column: 30)
!15 = distinct !DILexicalBlock(scope: !16, file: !1, line: 7, column: 5)
!16 = distinct !DILexicalBlock(scope: !7, file: !1, line: 7, column: 5)
!17 = !DILocalVariable(name: "j", scope: !18, file: !1, line: 9, type: !10)
!18 = distinct !DILexicalBlock(scope: !14, file: !1, line: 9, column: 7)
!19 = !DILocalVariable(name: "b", scope: !20, file: !1, line: 10, type: !10)
!20 = distinct !DILexicalBlock(scope: !21, file: !1, line: 9, column: 37)
!21 = distinct !DILexicalBlock(scope: !18, file: !1, line: 9, column: 7)
!22 = !DILocation(line: 0, scope: !7)
!23 = !DILocation(line: 7, column: 5, scope: !16)
!24 = !DILocation(line: 0, scope: !18)
!25 = !DILocation(line: 9, column: 25, scope: !21)
!26 = !DILocation(line: 9, column: 7, scope: !18)
!27 = !DILocation(line: 10, column: 17, scope: !20)
!28 = !DILocation(line: 0, scope: !20)
!29 = !DILocation(line: 11, column: 9, scope: !20)
!30 = !DILocation(line: 13, column: 13, scope: !31)
!31 = distinct !DILexicalBlock(scope: !20, file: !1, line: 11, column: 20)
!32 = !DILocation(line: 13, column: 17, scope: !31)
!33 = !DILocation(line: 0, scope: !16)
!34 = !DILocation(line: 9, column: 33, scope: !21)
!35 = distinct !{!35, !26, !36}
!36 = !DILocation(line: 17, column: 7, scope: !18)
!37 = !DILocation(line: 7, column: 12, scope: !16)
!38 = !DILocation(line: 7, column: 26, scope: !15)
!39 = !DILocation(line: 7, column: 19, scope: !15)
!40 = distinct !{!40, !23, !41}
!41 = !DILocation(line: 18, column: 5, scope: !16)
!42 = !DILocation(line: 19, column: 23, scope: !7)
!43 = !DILocation(line: 19, column: 21, scope: !7)
!44 = !DILocation(line: 19, column: 5, scope: !7)
!45 = !DILocation(line: 21, column: 5, scope: !7)
!46 = !DILocation(line: 22, column: 1, scope: !7)
