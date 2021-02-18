; ModuleID = 'issue_478.bc'
source_filename = "test-data/golden/golden-loop-merging/issue_478.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"x\00", align 1
@.str.1 = private unnamed_addr constant [2 x i8] c"y\00", align 1
@.str.2 = private unnamed_addr constant [49 x i8] c"test-data/golden/golden-loop-merging/issue_478.c\00", align 1

; Function Attrs: nounwind uwtable
define dso_local i32 @bad() local_unnamed_addr #0 !dbg !13 {
  call void @llvm.dbg.value(metadata i32 0, metadata !18, metadata !DIExpression()), !dbg !24
  br label %1, !dbg !25

1:                                                ; preds = %0, %11
  %2 = phi i32 [ 0, %0 ], [ %13, %11 ]
  call void @llvm.dbg.value(metadata i32 %2, metadata !18, metadata !DIExpression()), !dbg !24
  %3 = tail call signext i8 @crucible_int8_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0)) #3, !dbg !26
  call void @llvm.dbg.value(metadata i8 %3, metadata !19, metadata !DIExpression()), !dbg !27
  %4 = tail call signext i8 @crucible_int8_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1, i64 0, i64 0)) #3, !dbg !28
  call void @llvm.dbg.value(metadata i8 %4, metadata !23, metadata !DIExpression()), !dbg !27
  %5 = icmp ugt i8 %3, 100, !dbg !29
  br i1 %5, label %6, label %11, !dbg !31

6:                                                ; preds = %1
  %7 = icmp ugt i8 %4, 100, !dbg !32
  %8 = xor i1 %7, true, !dbg !35
  %9 = zext i1 %8 to i32, !dbg !35
  %10 = add nsw i32 %2, %9, !dbg !35
  call void @llvm.dbg.value(metadata i32 %10, metadata !18, metadata !DIExpression()), !dbg !24
  br i1 %7, label %15, label %11

11:                                               ; preds = %6, %1
  %12 = phi i32 [ %10, %6 ], [ %2, %1 ]
  %13 = add nsw i32 %12, 1, !dbg !36
  call void @llvm.dbg.value(metadata i32 %13, metadata !18, metadata !DIExpression()), !dbg !24
  %14 = icmp slt i32 %13, 15, !dbg !37
  br i1 %14, label %1, label %15, !dbg !25, !llvm.loop !38

15:                                               ; preds = %6, %11
  %16 = phi i32 [ 15, %6 ], [ %13, %11 ], !dbg !24
  ret i32 %16, !dbg !40
}

declare dso_local signext i8 @crucible_int8_t(i8*) local_unnamed_addr #1

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #0 !dbg !41 {
  %1 = tail call i32 @bad(), !dbg !44
  call void @llvm.dbg.value(metadata i32 %1, metadata !43, metadata !DIExpression()), !dbg !45
  %2 = add i32 %1, -15, !dbg !46
  %3 = icmp ult i32 %2, 2, !dbg !46
  %4 = zext i1 %3 to i8, !dbg !47
  tail call void @crucible_assert(i8 zeroext %4, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.2, i64 0, i64 0), i32 24) #3, !dbg !48
  ret i32 0, !dbg !49
}

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) local_unnamed_addr #1

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.value(metadata, metadata, metadata) #2

attributes #0 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind readnone speculatable }
attributes #3 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!9, !10, !11}
!llvm.ident = !{!12}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !3, nameTableKind: None)
!1 = !DIFile(filename: "test-data/golden/golden-loop-merging/issue_478.c", directory: "/home/abakst/crucible/crux-llvm")
!2 = !{}
!3 = !{!4}
!4 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint8_t", file: !5, line: 24, baseType: !6)
!5 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h", directory: "")
!6 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint8_t", file: !7, line: 37, baseType: !8)
!7 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types.h", directory: "")
!8 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!9 = !{i32 2, !"Dwarf Version", i32 4}
!10 = !{i32 2, !"Debug Info Version", i32 3}
!11 = !{i32 1, !"wchar_size", i32 4}
!12 = !{!"clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)"}
!13 = distinct !DISubprogram(name: "bad", scope: !1, file: !1, line: 6, type: !14, scopeLine: 6, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !17)
!14 = !DISubroutineType(types: !15)
!15 = !{!16}
!16 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!17 = !{!18, !19, !23}
!18 = !DILocalVariable(name: "i", scope: !13, file: !1, line: 7, type: !16)
!19 = !DILocalVariable(name: "x", scope: !20, file: !1, line: 9, type: !4)
!20 = distinct !DILexicalBlock(scope: !21, file: !1, line: 8, column: 29)
!21 = distinct !DILexicalBlock(scope: !22, file: !1, line: 8, column: 5)
!22 = distinct !DILexicalBlock(scope: !13, file: !1, line: 8, column: 5)
!23 = !DILocalVariable(name: "y", scope: !20, file: !1, line: 10, type: !4)
!24 = !DILocation(line: 0, scope: !13)
!25 = !DILocation(line: 8, column: 5, scope: !22)
!26 = !DILocation(line: 9, column: 21, scope: !20)
!27 = !DILocation(line: 0, scope: !20)
!28 = !DILocation(line: 10, column: 21, scope: !20)
!29 = !DILocation(line: 12, column: 17, scope: !30)
!30 = distinct !DILexicalBlock(scope: !20, file: !1, line: 12, column: 13)
!31 = !DILocation(line: 12, column: 13, scope: !20)
!32 = !DILocation(line: 13, column: 21, scope: !33)
!33 = distinct !DILexicalBlock(scope: !34, file: !1, line: 13, column: 17)
!34 = distinct !DILexicalBlock(scope: !30, file: !1, line: 12, column: 22)
!35 = !DILocation(line: 13, column: 17, scope: !34)
!36 = !DILocation(line: 8, column: 24, scope: !21)
!37 = !DILocation(line: 8, column: 19, scope: !21)
!38 = distinct !{!38, !25, !39}
!39 = !DILocation(line: 18, column: 5, scope: !22)
!40 = !DILocation(line: 20, column: 1, scope: !13)
!41 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 22, type: !14, scopeLine: 22, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !42)
!42 = !{!43}
!43 = !DILocalVariable(name: "i", scope: !41, file: !1, line: 23, type: !16)
!44 = !DILocation(line: 23, column: 13, scope: !41)
!45 = !DILocation(line: 0, scope: !41)
!46 = !DILocation(line: 24, column: 30, scope: !41)
!47 = !DILocation(line: 24, column: 22, scope: !41)
!48 = !DILocation(line: 24, column: 5, scope: !41)
!49 = !DILocation(line: 25, column: 1, scope: !41)
