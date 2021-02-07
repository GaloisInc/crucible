; ModuleID = 'string2.bc'
source_filename = "test-data/golden/golden-loop-merging/string2.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"x\00", align 1
@.str.1 = private unnamed_addr constant [47 x i8] c"test-data/golden/golden-loop-merging/string2.c\00", align 1

; Function Attrs: norecurse nounwind readonly uwtable
define dso_local i32 @string_length(i8* nocapture readonly) local_unnamed_addr #0 !dbg !7 {
  call void @llvm.dbg.value(metadata i8* %0, metadata !15, metadata !DIExpression()), !dbg !18
  call void @llvm.dbg.value(metadata i32 0, metadata !16, metadata !DIExpression()), !dbg !18
  call void @llvm.dbg.value(metadata i32 0, metadata !17, metadata !DIExpression()), !dbg !18
  %2 = load i8, i8* %0, align 1, !dbg !19, !tbaa !20
  %3 = icmp eq i8 %2, 0, !dbg !23
  br i1 %3, label %12, label %4, !dbg !24

4:                                                ; preds = %1, %4
  %5 = phi i64 [ %7, %4 ], [ 0, %1 ]
  %6 = phi i32 [ %8, %4 ], [ 0, %1 ]
  call void @llvm.dbg.value(metadata i64 %5, metadata !17, metadata !DIExpression()), !dbg !18
  call void @llvm.dbg.value(metadata i32 %6, metadata !16, metadata !DIExpression()), !dbg !18
  %7 = add nuw i64 %5, 1, !dbg !25
  %8 = add nuw nsw i32 %6, 1, !dbg !25
  call void @llvm.dbg.value(metadata i32 %8, metadata !17, metadata !DIExpression()), !dbg !18
  call void @llvm.dbg.value(metadata i32 %8, metadata !16, metadata !DIExpression()), !dbg !18
  %9 = getelementptr inbounds i8, i8* %0, i64 %7, !dbg !19
  %10 = load i8, i8* %9, align 1, !dbg !19, !tbaa !20
  %11 = icmp eq i8 %10, 0, !dbg !23
  br i1 %11, label %12, label %4, !dbg !24, !llvm.loop !27

12:                                               ; preds = %4, %1
  %13 = phi i32 [ 0, %1 ], [ %8, %4 ], !dbg !18
  call void @llvm.dbg.value(metadata i32 %13, metadata !16, metadata !DIExpression()), !dbg !18
  ret i32 %13, !dbg !29
}

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #1 !dbg !30 {
  %1 = tail call i8* @crucible_string(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0), i64 5) #4, !dbg !35
  call void @llvm.dbg.value(metadata i8* %1, metadata !34, metadata !DIExpression()), !dbg !36
  %2 = load i8, i8* %1, align 1, !dbg !37, !tbaa !20
  %3 = add i8 %2, -6, !dbg !37
  %4 = icmp ult i8 %3, 14, !dbg !37
  %5 = zext i1 %4 to i8, !dbg !37
  tail call void @crucible_assume(i8 zeroext %5, i8* getelementptr inbounds ([47 x i8], [47 x i8]* @.str.1, i64 0, i64 0), i32 16) #4, !dbg !37
  %6 = getelementptr inbounds i8, i8* %1, i64 1, !dbg !38
  %7 = load i8, i8* %6, align 1, !dbg !38, !tbaa !20
  %8 = add i8 %7, -6, !dbg !38
  %9 = icmp ult i8 %8, 4, !dbg !38
  %10 = zext i1 %9 to i8, !dbg !38
  tail call void @crucible_assume(i8 zeroext %10, i8* getelementptr inbounds ([47 x i8], [47 x i8]* @.str.1, i64 0, i64 0), i32 17) #4, !dbg !38
  %11 = getelementptr inbounds i8, i8* %1, i64 3, !dbg !39
  %12 = load i8, i8* %11, align 1, !dbg !39, !tbaa !20
  %13 = icmp eq i8 %12, 0, !dbg !39
  %14 = zext i1 %13 to i8, !dbg !39
  tail call void @crucible_assume(i8 zeroext %14, i8* getelementptr inbounds ([47 x i8], [47 x i8]* @.str.1, i64 0, i64 0), i32 18) #4, !dbg !39
  %15 = load i8, i8* %1, align 1, !dbg !40, !tbaa !20
  %16 = sext i8 %15 to i32, !dbg !40
  %17 = load i8, i8* %6, align 1, !dbg !40, !tbaa !20
  %18 = sext i8 %17 to i32, !dbg !40
  %19 = add nsw i32 %18, %16, !dbg !40
  %20 = icmp sgt i32 %19, 5, !dbg !40
  %21 = zext i1 %20 to i8, !dbg !40
  tail call void @crucible_assert(i8 zeroext %21, i8* getelementptr inbounds ([47 x i8], [47 x i8]* @.str.1, i64 0, i64 0), i32 19) #4, !dbg !40
  %22 = tail call i32 @string_length(i8* %1), !dbg !41
  %23 = icmp slt i32 %22, 5, !dbg !41
  %24 = zext i1 %23 to i8, !dbg !41
  tail call void @crucible_assert(i8 zeroext %24, i8* getelementptr inbounds ([47 x i8], [47 x i8]* @.str.1, i64 0, i64 0), i32 20) #4, !dbg !41
  ret i32 0, !dbg !42
}

declare dso_local i8* @crucible_string(i8*, i64) local_unnamed_addr #2

declare dso_local void @crucible_assume(i8 zeroext, i8*, i32) local_unnamed_addr #2

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) local_unnamed_addr #2

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.value(metadata, metadata, metadata) #3

attributes #0 = { norecurse nounwind readonly uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind readnone speculatable }
attributes #4 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5}
!llvm.ident = !{!6}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, nameTableKind: None)
!1 = !DIFile(filename: "test-data/golden/golden-loop-merging/string2.c", directory: "/home/abakst/crucible/crux-llvm")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)"}
!7 = distinct !DISubprogram(name: "string_length", scope: !1, file: !1, line: 3, type: !8, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !14)
!8 = !DISubroutineType(types: !9)
!9 = !{!10, !11}
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !12, size: 64)
!12 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !13)
!13 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!14 = !{!15, !16, !17}
!15 = !DILocalVariable(name: "str", arg: 1, scope: !7, file: !1, line: 3, type: !11)
!16 = !DILocalVariable(name: "len", scope: !7, file: !1, line: 4, type: !10)
!17 = !DILocalVariable(name: "i", scope: !7, file: !1, line: 5, type: !10)
!18 = !DILocation(line: 0, scope: !7)
!19 = !DILocation(line: 6, column: 9, scope: !7)
!20 = !{!21, !21, i64 0}
!21 = !{!"omnipotent char", !22, i64 0}
!22 = !{!"Simple C/C++ TBAA"}
!23 = !DILocation(line: 6, column: 16, scope: !7)
!24 = !DILocation(line: 6, column: 3, scope: !7)
!25 = !DILocation(line: 7, column: 6, scope: !26)
!26 = distinct !DILexicalBlock(scope: !7, file: !1, line: 6, column: 25)
!27 = distinct !{!27, !24, !28}
!28 = !DILocation(line: 9, column: 3, scope: !7)
!29 = !DILocation(line: 11, column: 3, scope: !7)
!30 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 14, type: !31, scopeLine: 14, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !33)
!31 = !DISubroutineType(types: !32)
!32 = !{!10}
!33 = !{!34}
!34 = !DILocalVariable(name: "str", scope: !30, file: !1, line: 15, type: !11)
!35 = !DILocation(line: 15, column: 21, scope: !30)
!36 = !DILocation(line: 0, scope: !30)
!37 = !DILocation(line: 16, column: 3, scope: !30)
!38 = !DILocation(line: 17, column: 3, scope: !30)
!39 = !DILocation(line: 18, column: 3, scope: !30)
!40 = !DILocation(line: 19, column: 3, scope: !30)
!41 = !DILocation(line: 20, column: 3, scope: !30)
!42 = !DILocation(line: 21, column: 3, scope: !30)
