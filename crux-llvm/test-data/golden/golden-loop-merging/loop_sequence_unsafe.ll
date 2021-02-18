; ModuleID = 'loop_sequence_unsafe.bc'
source_filename = "test-data/golden/golden-loop-merging/loop_sequence_unsafe.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"b\00", align 1
@.str.1 = private unnamed_addr constant [60 x i8] c"test-data/golden/golden-loop-merging/loop_sequence_unsafe.c\00", align 1

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #0 !dbg !7 {
  call void @llvm.dbg.value(metadata i32 0, metadata !12, metadata !DIExpression()), !dbg !22
  br label %1, !dbg !23

1:                                                ; preds = %0, %6
  %2 = phi i32 [ 0, %0 ], [ %8, %6 ]
  call void @llvm.dbg.value(metadata i32 %2, metadata !12, metadata !DIExpression()), !dbg !22
  %3 = tail call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0)) #3, !dbg !24
  call void @llvm.dbg.value(metadata i32 %3, metadata !13, metadata !DIExpression()), !dbg !25
  switch i32 %3, label %23 [
    i32 0, label %6
    i32 2, label %4
    i32 1, label %6
  ], !dbg !26

4:                                                ; preds = %1
  %5 = add nsw i32 %2, 1, !dbg !27
  call void @llvm.dbg.value(metadata i32 %5, metadata !12, metadata !DIExpression()), !dbg !22
  br label %6, !dbg !31

6:                                                ; preds = %1, %1, %4
  %7 = phi i32 [ %2, %1 ], [ %5, %4 ], [ %2, %1 ]
  call void @llvm.dbg.value(metadata i32 undef, metadata !12, metadata !DIExpression()), !dbg !22
  %8 = add nsw i32 %7, 1, !dbg !32
  call void @llvm.dbg.value(metadata i32 %8, metadata !12, metadata !DIExpression()), !dbg !22
  %9 = icmp slt i32 %8, 7, !dbg !33
  br i1 %9, label %1, label %10, !dbg !23, !llvm.loop !34

10:                                               ; preds = %6, %16
  %11 = phi i32 [ %18, %16 ], [ 0, %6 ]
  %12 = phi i32 [ %17, %16 ], [ %8, %6 ]
  call void @llvm.dbg.value(metadata i32 %11, metadata !17, metadata !DIExpression()), !dbg !36
  call void @llvm.dbg.value(metadata i32 %12, metadata !12, metadata !DIExpression()), !dbg !22
  %13 = tail call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0)) #3, !dbg !37
  call void @llvm.dbg.value(metadata i32 %13, metadata !19, metadata !DIExpression()), !dbg !38
  switch i32 %13, label %23 [
    i32 0, label %16
    i32 2, label %14
    i32 1, label %16
  ], !dbg !39

14:                                               ; preds = %10
  %15 = add nsw i32 %12, 7, !dbg !40
  call void @llvm.dbg.value(metadata i32 %15, metadata !12, metadata !DIExpression()), !dbg !22
  br label %16, !dbg !44

16:                                               ; preds = %14, %10, %10
  %17 = phi i32 [ %15, %14 ], [ %12, %10 ], [ %12, %10 ], !dbg !22
  %18 = add nuw nsw i32 %11, 1, !dbg !45
  call void @llvm.dbg.value(metadata i32 %18, metadata !17, metadata !DIExpression()), !dbg !36
  call void @llvm.dbg.value(metadata i32 %17, metadata !12, metadata !DIExpression()), !dbg !22
  %19 = icmp eq i32 %18, 7, !dbg !46
  br i1 %19, label %20, label %10, !dbg !47, !llvm.loop !48

20:                                               ; preds = %16
  call void @llvm.dbg.value(metadata i32 %17, metadata !12, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 %17, metadata !12, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 %17, metadata !12, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 %17, metadata !12, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 %17, metadata !12, metadata !DIExpression()), !dbg !22
  %21 = icmp ult i32 %17, 16, !dbg !50
  %22 = zext i1 %21 to i8, !dbg !51
  tail call void @crucible_assert(i8 zeroext %22, i8* getelementptr inbounds ([60 x i8], [60 x i8]* @.str.1, i64 0, i64 0), i32 32) #3, !dbg !52
  br label %23, !dbg !53

23:                                               ; preds = %1, %10, %20
  %24 = phi i32 [ 0, %20 ], [ %12, %10 ], [ %2, %1 ], !dbg !22
  ret i32 %24, !dbg !54
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
!1 = !DIFile(filename: "test-data/golden/golden-loop-merging/loop_sequence_unsafe.c", directory: "/home/abakst/crucible/crux-llvm")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)"}
!7 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 5, type: !8, scopeLine: 6, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !11)
!8 = !DISubroutineType(types: !9)
!9 = !{!10}
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !{!12, !13, !17, !19}
!12 = !DILocalVariable(name: "i", scope: !7, file: !1, line: 7, type: !10)
!13 = !DILocalVariable(name: "b", scope: !14, file: !1, line: 9, type: !10)
!14 = distinct !DILexicalBlock(scope: !15, file: !1, line: 8, column: 29)
!15 = distinct !DILexicalBlock(scope: !16, file: !1, line: 8, column: 5)
!16 = distinct !DILexicalBlock(scope: !7, file: !1, line: 8, column: 5)
!17 = !DILocalVariable(name: "j", scope: !18, file: !1, line: 21, type: !10)
!18 = distinct !DILexicalBlock(scope: !7, file: !1, line: 21, column: 5)
!19 = !DILocalVariable(name: "b", scope: !20, file: !1, line: 22, type: !10)
!20 = distinct !DILexicalBlock(scope: !21, file: !1, line: 21, column: 33)
!21 = distinct !DILexicalBlock(scope: !18, file: !1, line: 21, column: 5)
!22 = !DILocation(line: 0, scope: !7)
!23 = !DILocation(line: 8, column: 5, scope: !16)
!24 = !DILocation(line: 9, column: 17, scope: !14)
!25 = !DILocation(line: 0, scope: !14)
!26 = !DILocation(line: 10, column: 13, scope: !14)
!27 = !DILocation(line: 12, column: 13, scope: !28)
!28 = distinct !DILexicalBlock(scope: !29, file: !1, line: 11, column: 15)
!29 = distinct !DILexicalBlock(scope: !30, file: !1, line: 10, column: 21)
!30 = distinct !DILexicalBlock(scope: !14, file: !1, line: 10, column: 13)
!31 = !DILocation(line: 12, column: 12, scope: !28)
!32 = !DILocation(line: 8, column: 25, scope: !15)
!33 = !DILocation(line: 8, column: 19, scope: !15)
!34 = distinct !{!34, !23, !35}
!35 = !DILocation(line: 19, column: 5, scope: !16)
!36 = !DILocation(line: 0, scope: !18)
!37 = !DILocation(line: 22, column: 17, scope: !20)
!38 = !DILocation(line: 0, scope: !20)
!39 = !DILocation(line: 23, column: 13, scope: !20)
!40 = !DILocation(line: 25, column: 13, scope: !41)
!41 = distinct !DILexicalBlock(scope: !42, file: !1, line: 24, column: 15)
!42 = distinct !DILexicalBlock(scope: !43, file: !1, line: 23, column: 21)
!43 = distinct !DILexicalBlock(scope: !20, file: !1, line: 23, column: 13)
!44 = !DILocation(line: 25, column: 12, scope: !41)
!45 = !DILocation(line: 21, column: 29, scope: !21)
!46 = !DILocation(line: 21, column: 23, scope: !21)
!47 = !DILocation(line: 21, column: 5, scope: !18)
!48 = distinct !{!48, !47, !49}
!49 = !DILocation(line: 31, column: 5, scope: !18)
!50 = !DILocation(line: 32, column: 28, scope: !7)
!51 = !DILocation(line: 32, column: 21, scope: !7)
!52 = !DILocation(line: 32, column: 5, scope: !7)
!53 = !DILocation(line: 34, column: 5, scope: !7)
!54 = !DILocation(line: 35, column: 1, scope: !7)
