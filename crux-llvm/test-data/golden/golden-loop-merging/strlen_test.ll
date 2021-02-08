; ModuleID = 'strlen_test.bc'
source_filename = "test-data/golden/golden-loop-merging/strlen_test.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"x\00", align 1
@.str.1 = private unnamed_addr constant [51 x i8] c"test-data/golden/golden-loop-merging/strlen_test.c\00", align 1

; Function Attrs: nounwind uwtable
define dso_local noalias i8* @mkstr() local_unnamed_addr #0 !dbg !7 {
  %1 = tail call noalias i8* @malloc(i64 10) #5, !dbg !17
  call void @llvm.dbg.value(metadata i8* %1, metadata !13, metadata !DIExpression()), !dbg !18
  call void @llvm.dbg.value(metadata i32 0, metadata !14, metadata !DIExpression()), !dbg !19
  br label %7, !dbg !20

2:                                                ; preds = %7
  %3 = getelementptr inbounds i8, i8* %1, i64 9, !dbg !21
  %4 = load i8, i8* %3, align 1, !dbg !21, !tbaa !22
  %5 = icmp eq i8 %4, 0, !dbg !21
  %6 = zext i1 %5 to i8, !dbg !21
  tail call void @crucible_assume(i8 zeroext %6, i8* getelementptr inbounds ([51 x i8], [51 x i8]* @.str.1, i64 0, i64 0), i32 14) #5, !dbg !21
  ret i8* %1, !dbg !25

7:                                                ; preds = %7, %0
  %8 = phi i64 [ 0, %0 ], [ %11, %7 ]
  call void @llvm.dbg.value(metadata i64 %8, metadata !14, metadata !DIExpression()), !dbg !19
  %9 = tail call signext i8 @crucible_int8_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0)) #5, !dbg !26
  %10 = getelementptr inbounds i8, i8* %1, i64 %8, !dbg !29
  store i8 %9, i8* %10, align 1, !dbg !30, !tbaa !22
  %11 = add nuw nsw i64 %8, 1, !dbg !31
  call void @llvm.dbg.value(metadata i32 undef, metadata !14, metadata !DIExpression(DW_OP_plus_uconst, 1, DW_OP_stack_value)), !dbg !19
  %12 = icmp eq i64 %11, 10, !dbg !32
  br i1 %12, label %2, label %7, !dbg !20, !llvm.loop !33
}

; Function Attrs: nofree nounwind
declare dso_local noalias i8* @malloc(i64) local_unnamed_addr #1

declare dso_local signext i8 @crucible_int8_t(i8*) local_unnamed_addr #2

declare dso_local void @crucible_assume(i8 zeroext, i8*, i32) local_unnamed_addr #2

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #0 !dbg !35 {
  %1 = tail call i8* @mkstr(), !dbg !44
  call void @llvm.dbg.value(metadata i8* %1, metadata !39, metadata !DIExpression()), !dbg !45
  %2 = tail call i64 @strlen(i8* %1) #6, !dbg !46
  call void @llvm.dbg.value(metadata i64 %2, metadata !40, metadata !DIExpression()), !dbg !45
  %3 = icmp ult i64 %2, 10, !dbg !47
  %4 = zext i1 %3 to i8, !dbg !47
  tail call void @crucible_assert(i8 zeroext %4, i8* getelementptr inbounds ([51 x i8], [51 x i8]* @.str.1, i64 0, i64 0), i32 22) #5, !dbg !47
  ret i32 0, !dbg !48
}

; Function Attrs: argmemonly nofree nounwind readonly
declare dso_local i64 @strlen(i8* nocapture) local_unnamed_addr #3

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) local_unnamed_addr #2

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.value(metadata, metadata, metadata) #4

attributes #0 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nofree nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nofree nounwind readonly "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind readnone speculatable }
attributes #5 = { nounwind }
attributes #6 = { nounwind readonly }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5}
!llvm.ident = !{!6}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, nameTableKind: None)
!1 = !DIFile(filename: "test-data/golden/golden-loop-merging/strlen_test.c", directory: "/home/abakst/crucible/crux-llvm")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)"}
!7 = distinct !DISubprogram(name: "mkstr", scope: !1, file: !1, line: 8, type: !8, scopeLine: 8, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !12)
!8 = !DISubroutineType(types: !9)
!9 = !{!10}
!10 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !11, size: 64)
!11 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!12 = !{!13, !14}
!13 = !DILocalVariable(name: "x", scope: !7, file: !1, line: 9, type: !10)
!14 = !DILocalVariable(name: "i", scope: !15, file: !1, line: 10, type: !16)
!15 = distinct !DILexicalBlock(scope: !7, file: !1, line: 10, column: 3)
!16 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!17 = !DILocation(line: 9, column: 13, scope: !7)
!18 = !DILocation(line: 0, scope: !7)
!19 = !DILocation(line: 0, scope: !15)
!20 = !DILocation(line: 10, column: 3, scope: !15)
!21 = !DILocation(line: 14, column: 3, scope: !7)
!22 = !{!23, !23, i64 0}
!23 = !{!"omnipotent char", !24, i64 0}
!24 = !{!"Simple C/C++ TBAA"}
!25 = !DILocation(line: 16, column: 3, scope: !7)
!26 = !DILocation(line: 11, column: 12, scope: !27)
!27 = distinct !DILexicalBlock(scope: !28, file: !1, line: 10, column: 30)
!28 = distinct !DILexicalBlock(scope: !15, file: !1, line: 10, column: 3)
!29 = !DILocation(line: 11, column: 5, scope: !27)
!30 = !DILocation(line: 11, column: 10, scope: !27)
!31 = !DILocation(line: 10, column: 25, scope: !28)
!32 = !DILocation(line: 10, column: 18, scope: !28)
!33 = distinct !{!33, !20, !34}
!34 = !DILocation(line: 12, column: 3, scope: !15)
!35 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 19, type: !36, scopeLine: 19, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !38)
!36 = !DISubroutineType(types: !37)
!37 = !{!16}
!38 = !{!39, !40}
!39 = !DILocalVariable(name: "str", scope: !35, file: !1, line: 20, type: !10)
!40 = !DILocalVariable(name: "sz", scope: !35, file: !1, line: 21, type: !41)
!41 = !DIDerivedType(tag: DW_TAG_typedef, name: "size_t", file: !42, line: 46, baseType: !43)
!42 = !DIFile(filename: "/usr/lib/llvm-9/lib/clang/9.0.0/include/stddef.h", directory: "")
!43 = !DIBasicType(name: "long unsigned int", size: 64, encoding: DW_ATE_unsigned)
!44 = !DILocation(line: 20, column: 15, scope: !35)
!45 = !DILocation(line: 0, scope: !35)
!46 = !DILocation(line: 21, column: 15, scope: !35)
!47 = !DILocation(line: 22, column: 3, scope: !35)
!48 = !DILocation(line: 23, column: 1, scope: !35)
