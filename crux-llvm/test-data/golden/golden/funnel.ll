; ModuleID = 'funnel.c'
source_filename = "funnel.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@.str = private unnamed_addr constant [2 x i8] c"x\00", align 1
@.str.1 = private unnamed_addr constant [2 x i8] c"y\00", align 1
@.str.2 = private unnamed_addr constant [2 x i8] c"a\00", align 1
@__func__.main = private unnamed_addr constant [5 x i8] c"main\00", align 1
@.str.3 = private unnamed_addr constant [9 x i8] c"funnel.c\00", align 1
@.str.4 = private unnamed_addr constant [46 x i8] c"builtin_fshl32( x, y, a) == fshl32( x, y, a )\00", align 1
@.str.5 = private unnamed_addr constant [46 x i8] c"builtin_fshr32( x, y, a) == fshr32( x, y, a )\00", align 1

declare i32 @llvm.fshl.i32(i32, i32, i32)
declare i32 @llvm.fshr.i32(i32, i32, i32)

; Function Attrs: nounwind readnone ssp uwtable
define i32 @fshl32(i32, i32, i32) local_unnamed_addr #0 !dbg !15 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !19, metadata !DIExpression()), !dbg !24
  call void @llvm.dbg.value(metadata i32 %1, metadata !20, metadata !DIExpression()), !dbg !25
  call void @llvm.dbg.value(metadata i32 %2, metadata !21, metadata !DIExpression()), !dbg !26
  %4 = zext i32 %0 to i64, !dbg !27
  %5 = shl nuw i64 %4, 32, !dbg !28
  %6 = zext i32 %1 to i64, !dbg !29
  %7 = or i64 %5, %6, !dbg !30
  call void @llvm.dbg.value(metadata i64 %7, metadata !22, metadata !DIExpression()), !dbg !31
  %8 = and i32 %2, 31, !dbg !32
  %9 = zext i32 %8 to i64, !dbg !33
  %10 = shl i64 %7, %9, !dbg !34
  call void @llvm.dbg.value(metadata i64 %10, metadata !23, metadata !DIExpression()), !dbg !35
  %11 = lshr i64 %10, 32, !dbg !36
  %12 = trunc i64 %11 to i32, !dbg !37
  ret i32 %12, !dbg !38
}

; Function Attrs: nounwind readnone ssp uwtable
define i32 @fshr32(i32, i32, i32) local_unnamed_addr #0 !dbg !39 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !41, metadata !DIExpression()), !dbg !46
  call void @llvm.dbg.value(metadata i32 %1, metadata !42, metadata !DIExpression()), !dbg !47
  call void @llvm.dbg.value(metadata i32 %2, metadata !43, metadata !DIExpression()), !dbg !48
  %4 = zext i32 %0 to i64, !dbg !49
  %5 = shl nuw i64 %4, 32, !dbg !50
  %6 = zext i32 %1 to i64, !dbg !51
  %7 = or i64 %5, %6, !dbg !52
  call void @llvm.dbg.value(metadata i64 %7, metadata !44, metadata !DIExpression()), !dbg !53
  %8 = and i32 %2, 31, !dbg !54
  %9 = zext i32 %8 to i64, !dbg !55
  %10 = lshr i64 %7, %9, !dbg !56
  call void @llvm.dbg.value(metadata i64 %10, metadata !45, metadata !DIExpression()), !dbg !57
  %11 = trunc i64 %10 to i32, !dbg !58
  ret i32 %11, !dbg !59
}

; Function Attrs: nounwind readnone ssp uwtable
define i32 @builtin_fshl32(i32, i32, i32) local_unnamed_addr #0 !dbg !60 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !62, metadata !DIExpression()), !dbg !65
  call void @llvm.dbg.value(metadata i32 %1, metadata !63, metadata !DIExpression()), !dbg !66
  call void @llvm.dbg.value(metadata i32 %2, metadata !64, metadata !DIExpression()), !dbg !67
  %4 = tail call i32 @llvm.fshl.i32(i32 %0, i32 %1, i32 %2), !dbg !68
  ret i32 %4, !dbg !69
}

; Function Attrs: nounwind readnone ssp uwtable
define i32 @builtin_fshr32(i32, i32, i32) local_unnamed_addr #0 !dbg !70 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !72, metadata !DIExpression()), !dbg !75
  call void @llvm.dbg.value(metadata i32 %1, metadata !73, metadata !DIExpression()), !dbg !76
  call void @llvm.dbg.value(metadata i32 %2, metadata !74, metadata !DIExpression()), !dbg !77
  %4 = tail call i32 @llvm.fshr.i32(i32 %0, i32 %1, i32 %2), !dbg !78
  ret i32 %4, !dbg !79
}

; Function Attrs: nounwind ssp uwtable
define i32 @main() local_unnamed_addr #1 !dbg !80 {
  %1 = tail call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0)) #5, !dbg !88
  call void @llvm.dbg.value(metadata i32 %1, metadata !85, metadata !DIExpression()), !dbg !89
  %2 = tail call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1, i64 0, i64 0)) #5, !dbg !90
  call void @llvm.dbg.value(metadata i32 %2, metadata !86, metadata !DIExpression()), !dbg !91
  %3 = tail call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0)) #5, !dbg !92
  call void @llvm.dbg.value(metadata i32 %3, metadata !87, metadata !DIExpression()), !dbg !93
  %4 = tail call i32 @builtin_fshl32(i32 %1, i32 %2, i32 %3), !dbg !94
  %5 = tail call i32 @fshl32(i32 %1, i32 %2, i32 %3), !dbg !94
  %6 = icmp eq i32 %4, %5, !dbg !94
  br i1 %6, label %8, label %7, !dbg !94, !prof !95

; <label>:7:                                      ; preds = %0
  tail call void @__assert_rtn(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @__func__.main, i64 0, i64 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.3, i64 0, i64 0), i32 34, i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.4, i64 0, i64 0)) #6, !dbg !94
  unreachable, !dbg !94

; <label>:8:                                      ; preds = %0
  %9 = tail call i32 @builtin_fshr32(i32 %1, i32 %2, i32 %3), !dbg !96
  %10 = tail call i32 @fshr32(i32 %1, i32 %2, i32 %3), !dbg !96
  %11 = icmp eq i32 %9, %10, !dbg !96
  br i1 %11, label %13, label %12, !dbg !96, !prof !95

; <label>:12:                                     ; preds = %8
  tail call void @__assert_rtn(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @__func__.main, i64 0, i64 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.3, i64 0, i64 0), i32 35, i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.5, i64 0, i64 0)) #6, !dbg !96
  unreachable, !dbg !96

; <label>:13:                                     ; preds = %8
  ret i32 0, !dbg !97
}

declare i32 @crucible_int32_t(i8*) local_unnamed_addr #2

; Function Attrs: cold noreturn
declare void @__assert_rtn(i8*, i8*, i32, i8*) local_unnamed_addr #3

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.value(metadata, metadata, metadata) #4

attributes #0 = { nounwind readnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { cold noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="true" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind readnone speculatable }
attributes #5 = { nounwind }
attributes #6 = { cold noreturn nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!10, !11, !12, !13}
!llvm.ident = !{!14}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 7.1.0 (tags/RELEASE_710/final)", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !3)
!1 = !DIFile(filename: "funnel.c", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
!2 = !{}
!3 = !{!4, !7}
!4 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint64_t", file: !5, line: 31, baseType: !6)
!5 = !DIFile(filename: "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/_types/_uint64_t.h", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
!6 = !DIBasicType(name: "long long unsigned int", size: 64, encoding: DW_ATE_unsigned)
!7 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint32_t", file: !8, line: 31, baseType: !9)
!8 = !DIFile(filename: "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/_types/_uint32_t.h", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
!9 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!10 = !{i32 2, !"Dwarf Version", i32 4}
!11 = !{i32 2, !"Debug Info Version", i32 3}
!12 = !{i32 1, !"wchar_size", i32 4}
!13 = !{i32 7, !"PIC Level", i32 2}
!14 = !{!"clang version 7.1.0 (tags/RELEASE_710/final)"}
!15 = distinct !DISubprogram(name: "fshl32", scope: !1, file: !1, line: 7, type: !16, isLocal: false, isDefinition: true, scopeLine: 7, flags: DIFlagPrototyped, isOptimized: true, unit: !0, retainedNodes: !18)
!16 = !DISubroutineType(types: !17)
!17 = !{!7, !7, !7, !7}
!18 = !{!19, !20, !21, !22, !23}
!19 = !DILocalVariable(name: "x", arg: 1, scope: !15, file: !1, line: 7, type: !7)
!20 = !DILocalVariable(name: "y", arg: 2, scope: !15, file: !1, line: 7, type: !7)
!21 = !DILocalVariable(name: "a", arg: 3, scope: !15, file: !1, line: 7, type: !7)
!22 = !DILocalVariable(name: "xy", scope: !15, file: !1, line: 8, type: !4)
!23 = !DILocalVariable(name: "z", scope: !15, file: !1, line: 9, type: !4)
!24 = !DILocation(line: 7, column: 27, scope: !15)
!25 = !DILocation(line: 7, column: 39, scope: !15)
!26 = !DILocation(line: 7, column: 51, scope: !15)
!27 = !DILocation(line: 8, column: 19, scope: !15)
!28 = !DILocation(line: 8, column: 32, scope: !15)
!29 = !DILocation(line: 8, column: 42, scope: !15)
!30 = !DILocation(line: 8, column: 39, scope: !15)
!31 = !DILocation(line: 8, column: 12, scope: !15)
!32 = !DILocation(line: 9, column: 37, scope: !15)
!33 = !DILocation(line: 9, column: 23, scope: !15)
!34 = !DILocation(line: 9, column: 20, scope: !15)
!35 = !DILocation(line: 9, column: 12, scope: !15)
!36 = !DILocation(line: 11, column: 25, scope: !15)
!37 = !DILocation(line: 11, column: 11, scope: !15)
!38 = !DILocation(line: 11, column: 3, scope: !15)
!39 = distinct !DISubprogram(name: "fshr32", scope: !1, file: !1, line: 14, type: !16, isLocal: false, isDefinition: true, scopeLine: 14, flags: DIFlagPrototyped, isOptimized: true, unit: !0, retainedNodes: !40)
!40 = !{!41, !42, !43, !44, !45}
!41 = !DILocalVariable(name: "x", arg: 1, scope: !39, file: !1, line: 14, type: !7)
!42 = !DILocalVariable(name: "y", arg: 2, scope: !39, file: !1, line: 14, type: !7)
!43 = !DILocalVariable(name: "a", arg: 3, scope: !39, file: !1, line: 14, type: !7)
!44 = !DILocalVariable(name: "xy", scope: !39, file: !1, line: 15, type: !4)
!45 = !DILocalVariable(name: "z", scope: !39, file: !1, line: 16, type: !4)
!46 = !DILocation(line: 14, column: 27, scope: !39)
!47 = !DILocation(line: 14, column: 39, scope: !39)
!48 = !DILocation(line: 14, column: 51, scope: !39)
!49 = !DILocation(line: 15, column: 19, scope: !39)
!50 = !DILocation(line: 15, column: 32, scope: !39)
!51 = !DILocation(line: 15, column: 42, scope: !39)
!52 = !DILocation(line: 15, column: 39, scope: !39)
!53 = !DILocation(line: 15, column: 12, scope: !39)
!54 = !DILocation(line: 16, column: 37, scope: !39)
!55 = !DILocation(line: 16, column: 23, scope: !39)
!56 = !DILocation(line: 16, column: 20, scope: !39)
!57 = !DILocation(line: 16, column: 12, scope: !39)
!58 = !DILocation(line: 18, column: 11, scope: !39)
!59 = !DILocation(line: 18, column: 3, scope: !39)
!60 = distinct !DISubprogram(name: "builtin_fshl32", scope: !1, file: !1, line: 21, type: !16, isLocal: false, isDefinition: true, scopeLine: 21, flags: DIFlagPrototyped, isOptimized: true, unit: !0, retainedNodes: !61)
!61 = !{!62, !63, !64}
!62 = !DILocalVariable(name: "x", arg: 1, scope: !60, file: !1, line: 21, type: !7)
!63 = !DILocalVariable(name: "y", arg: 2, scope: !60, file: !1, line: 21, type: !7)
!64 = !DILocalVariable(name: "a", arg: 3, scope: !60, file: !1, line: 21, type: !7)
!65 = !DILocation(line: 21, column: 35, scope: !60)
!66 = !DILocation(line: 21, column: 47, scope: !60)
!67 = !DILocation(line: 21, column: 59, scope: !60)
!68 = !DILocation(line: 22, column: 10, scope: !60)
!69 = !DILocation(line: 22, column: 3, scope: !60)
!70 = distinct !DISubprogram(name: "builtin_fshr32", scope: !1, file: !1, line: 25, type: !16, isLocal: false, isDefinition: true, scopeLine: 25, flags: DIFlagPrototyped, isOptimized: true, unit: !0, retainedNodes: !71)
!71 = !{!72, !73, !74}
!72 = !DILocalVariable(name: "x", arg: 1, scope: !70, file: !1, line: 25, type: !7)
!73 = !DILocalVariable(name: "y", arg: 2, scope: !70, file: !1, line: 25, type: !7)
!74 = !DILocalVariable(name: "a", arg: 3, scope: !70, file: !1, line: 25, type: !7)
!75 = !DILocation(line: 25, column: 35, scope: !70)
!76 = !DILocation(line: 25, column: 47, scope: !70)
!77 = !DILocation(line: 25, column: 59, scope: !70)
!78 = !DILocation(line: 26, column: 10, scope: !70)
!79 = !DILocation(line: 26, column: 3, scope: !70)
!80 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 29, type: !81, isLocal: false, isDefinition: true, scopeLine: 29, isOptimized: true, unit: !0, retainedNodes: !84)
!81 = !DISubroutineType(types: !82)
!82 = !{!83}
!83 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!84 = !{!85, !86, !87}
!85 = !DILocalVariable(name: "x", scope: !80, file: !1, line: 30, type: !7)
!86 = !DILocalVariable(name: "y", scope: !80, file: !1, line: 31, type: !7)
!87 = !DILocalVariable(name: "a", scope: !80, file: !1, line: 32, type: !7)
!88 = !DILocation(line: 30, column: 16, scope: !80)
!89 = !DILocation(line: 30, column: 12, scope: !80)
!90 = !DILocation(line: 31, column: 16, scope: !80)
!91 = !DILocation(line: 31, column: 12, scope: !80)
!92 = !DILocation(line: 32, column: 16, scope: !80)
!93 = !DILocation(line: 32, column: 12, scope: !80)
!94 = !DILocation(line: 34, column: 3, scope: !80)
!95 = !{!"branch_weights", i32 2000, i32 1}
!96 = !DILocation(line: 35, column: 3, scope: !80)
!97 = !DILocation(line: 37, column: 3, scope: !80)
