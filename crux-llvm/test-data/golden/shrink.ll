; ModuleID = 'shrink.c'
source_filename = "shrink.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

; Function Attrs: norecurse nounwind readnone ssp uwtable
define i32 @addflt(i32 %a, i32 %b) local_unnamed_addr #0 !dbg !11 {
entry:
  call void @llvm.dbg.value(metadata i32 %a, metadata !15, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 %b, metadata !16, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 %a, metadata !17, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 %b, metadata !18, metadata !DIExpression()), !dbg !22
  %shr = lshr i32 %a, 24, !dbg !23
  %sub = add nsw i32 %shr, -128, !dbg !24
  call void @llvm.dbg.value(metadata i32 %sub, metadata !19, metadata !DIExpression()), !dbg !22
  %shr1 = lshr i32 %b, 24, !dbg !25
  call void @llvm.dbg.value(metadata i32 %sub2.neg, metadata !20, metadata !DIExpression()), !dbg !22
  %sub2.neg = sub nsw i32 128, %shr1, !dbg !26
  %sub3 = add nsw i32 %sub2.neg, %sub, !dbg !27
  call void @llvm.dbg.value(metadata i32 %sub3, metadata !21, metadata !DIExpression()), !dbg !22
  %shr4 = lshr i32 %b, %sub3, !dbg !28
  call void @llvm.dbg.value(metadata i32 %shr4, metadata !18, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 undef, metadata !17, metadata !DIExpression()), !dbg !22
  %add = sub i32 0, %a, !dbg !29
  %tobool.not = icmp eq i32 %shr4, %add, !dbg !29
  %add5 = add nsw i32 %shr, -127
  %spec.select = select i1 %tobool.not, i32 %sub, i32 %add5, !dbg !31
  call void @llvm.dbg.value(metadata i32 %spec.select, metadata !19, metadata !DIExpression()), !dbg !22
  ret i32 %spec.select, !dbg !32
}

; Function Attrs: norecurse nounwind readnone ssp uwtable
define i32 @main() local_unnamed_addr #0 !dbg !33 {
entry:
  %call = call i32 @addflt(i32 2, i32 2), !dbg !36
  %tobool.not = icmp eq i32 %call, 0, !dbg !36
  %. = zext i1 %tobool.not to i32, !dbg !38
  ret i32 %., !dbg !39
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.value(metadata, metadata, metadata) #1

attributes #0 = { norecurse nounwind readnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!6, !7, !8, !9}
!llvm.ident = !{!10}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 11.1.0", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !3, nameTableKind: None, sysroot: "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk", sdk: "MacOSX.sdk")
!1 = !DIFile(filename: "shrink.c", directory: "/Users/rdockins/code/crucible/crux-llvm", checksumkind: CSK_MD5, checksum: "c2c71a098178ba3175febc60f68f1a59")
!2 = !{}
!3 = !{!4, !5}
!4 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!5 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!6 = !{i32 7, !"Dwarf Version", i32 5}
!7 = !{i32 2, !"Debug Info Version", i32 3}
!8 = !{i32 1, !"wchar_size", i32 4}
!9 = !{i32 7, !"PIC Level", i32 2}
!10 = !{!"clang version 11.1.0"}
!11 = distinct !DISubprogram(name: "addflt", scope: !1, file: !1, line: 1, type: !12, scopeLine: 2, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !14)
!12 = !DISubroutineType(types: !13)
!13 = !{!5, !5, !5}
!14 = !{!15, !16, !17, !18, !19, !20, !21}
!15 = !DILocalVariable(name: "a", arg: 1, scope: !11, file: !1, line: 1, type: !5)
!16 = !DILocalVariable(name: "b", arg: 2, scope: !11, file: !1, line: 1, type: !5)
!17 = !DILocalVariable(name: "ma", scope: !11, file: !1, line: 3, type: !5)
!18 = !DILocalVariable(name: "mb", scope: !11, file: !1, line: 4, type: !5)
!19 = !DILocalVariable(name: "ea", scope: !11, file: !1, line: 5, type: !4)
!20 = !DILocalVariable(name: "eb", scope: !11, file: !1, line: 6, type: !4)
!21 = !DILocalVariable(name: "delta", scope: !11, file: !1, line: 7, type: !5)
!22 = !DILocation(line: 0, scope: !11)
!23 = !DILocation(line: 5, column: 20, scope: !11)
!24 = !DILocation(line: 5, column: 28, scope: !11)
!25 = !DILocation(line: 6, column: 20, scope: !11)
!26 = !DILocation(line: 6, column: 28, scope: !11)
!27 = !DILocation(line: 7, column: 27, scope: !11)
!28 = !DILocation(line: 9, column: 11, scope: !11)
!29 = !DILocation(line: 13, column: 7, scope: !30)
!30 = distinct !DILexicalBlock(scope: !11, file: !1, line: 13, column: 7)
!31 = !DILocation(line: 13, column: 7, scope: !11)
!32 = !DILocation(line: 17, column: 3, scope: !11)
!33 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 20, type: !34, scopeLine: 21, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !2)
!34 = !DISubroutineType(types: !35)
!35 = !{!4}
!36 = !DILocation(line: 22, column: 7, scope: !37)
!37 = distinct !DILexicalBlock(scope: !33, file: !1, line: 22, column: 7)
!38 = !DILocation(line: 0, scope: !37)
!39 = !DILocation(line: 27, column: 1, scope: !33)
