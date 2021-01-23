; ModuleID = 'strlen_test2.bc'
source_filename = "test-data/golden/golden-loop-merging/strlen_test2.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [8 x i8] c"i = %u\0A\00", align 1
@.str.1 = private unnamed_addr constant [31 x i8] c"string[(length - i) - 1] = %u\0A\00", align 1
@.str.2 = private unnamed_addr constant [2 x i8] c"i\00", align 1
@.str.3 = private unnamed_addr constant [52 x i8] c"test-data/golden/golden-loop-merging/strlen_test2.c\00", align 1

; Function Attrs: nofree nounwind uwtable
define dso_local void @test(i8* nocapture readonly, i32) local_unnamed_addr #0 !dbg !7 {
  call void @llvm.dbg.value(metadata i8* %0, metadata !19, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 %1, metadata !20, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.value(metadata i32 0, metadata !21, metadata !DIExpression()), !dbg !22
  %3 = icmp eq i32 %1, 0, !dbg !23
  br i1 %3, label %23, label %4, !dbg !26

4:                                                ; preds = %2
  %5 = zext i32 %1 to i64, !dbg !26
  br label %6, !dbg !26

6:                                                ; preds = %4, %6
  %7 = phi i64 [ 0, %4 ], [ %18, %6 ]
  %8 = phi i32 [ 0, %4 ], [ %19, %6 ]
  call void @llvm.dbg.value(metadata i64 %7, metadata !21, metadata !DIExpression()), !dbg !22
  %9 = trunc i64 %7 to i32, !dbg !27
  %10 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str, i64 0, i64 0), i32 %9), !dbg !27
  %11 = xor i32 %8, -1, !dbg !29
  %12 = add i32 %11, %1, !dbg !29
  %13 = zext i32 %12 to i64, !dbg !30
  %14 = getelementptr inbounds i8, i8* %0, i64 %13, !dbg !30
  %15 = load i8, i8* %14, align 1, !dbg !30, !tbaa !31
  %16 = sext i8 %15 to i32, !dbg !30
  %17 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([31 x i8], [31 x i8]* @.str.1, i64 0, i64 0), i32 %16), !dbg !34
  %18 = add nuw nsw i64 %7, 1, !dbg !35
  %19 = add nuw nsw i32 %8, 1, !dbg !35
  call void @llvm.dbg.value(metadata i32 %19, metadata !21, metadata !DIExpression()), !dbg !22
  %20 = icmp ult i64 %18, %5, !dbg !23
  %21 = icmp ult i64 %18, 200, !dbg !36
  %22 = and i1 %20, %21, !dbg !36
  br i1 %22, label %6, label %23, !dbg !26, !llvm.loop !37

23:                                               ; preds = %6, %2
  ret void, !dbg !39
}

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #2

; Function Attrs: nofree nounwind
declare dso_local i32 @printf(i8* nocapture readonly, ...) local_unnamed_addr #3

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #2

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #4 !dbg !40 {
  %1 = alloca [100 x i8], align 16
  %2 = getelementptr inbounds [100 x i8], [100 x i8]* %1, i64 0, i64 0, !dbg !51
  call void @llvm.lifetime.start.p0i8(i64 100, i8* nonnull %2) #7, !dbg !51
  call void @llvm.dbg.declare(metadata [100 x i8]* %1, metadata !45, metadata !DIExpression()), !dbg !52
  call void @crucible_havoc_memory(i8* nonnull %2, i64 15) #7, !dbg !53
  %3 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0)) #7, !dbg !54
  call void @llvm.dbg.value(metadata i32 %3, metadata !49, metadata !DIExpression()), !dbg !55
  %4 = icmp ult i32 %3, 10, !dbg !56
  %5 = zext i1 %4 to i8, !dbg !56
  call void @crucible_assume(i8 zeroext %5, i8* getelementptr inbounds ([52 x i8], [52 x i8]* @.str.3, i64 0, i64 0), i32 37) #7, !dbg !56
  %6 = zext i32 %3 to i64, !dbg !57
  %7 = getelementptr inbounds [100 x i8], [100 x i8]* %1, i64 0, i64 %6, !dbg !57
  %8 = load i8, i8* %7, align 1, !dbg !57, !tbaa !31
  %9 = icmp eq i8 %8, 0, !dbg !57
  %10 = zext i1 %9 to i8, !dbg !57
  call void @crucible_assume(i8 zeroext %10, i8* getelementptr inbounds ([52 x i8], [52 x i8]* @.str.3, i64 0, i64 0), i32 38) #7, !dbg !57
  %11 = call i64 @strlen(i8* nonnull %2) #8, !dbg !58
  %12 = trunc i64 %11 to i32, !dbg !58
  call void @llvm.dbg.value(metadata i32 %12, metadata !50, metadata !DIExpression()), !dbg !55
  call void @test(i8* nonnull %2, i32 %12), !dbg !59
  %13 = icmp ult i32 %12, 10, !dbg !60
  %14 = zext i1 %13 to i8, !dbg !60
  call void @crucible_assert(i8 zeroext %14, i8* getelementptr inbounds ([52 x i8], [52 x i8]* @.str.3, i64 0, i64 0), i32 43) #7, !dbg !60
  call void @llvm.lifetime.end.p0i8(i64 100, i8* nonnull %2) #7, !dbg !61
  ret i32 0, !dbg !62
}

declare dso_local void @crucible_havoc_memory(i8*, i64) local_unnamed_addr #5

declare dso_local i32 @crucible_int32_t(i8*) local_unnamed_addr #5

declare dso_local void @crucible_assume(i8 zeroext, i8*, i32) local_unnamed_addr #5

; Function Attrs: argmemonly nofree nounwind readonly
declare dso_local i64 @strlen(i8* nocapture) local_unnamed_addr #6

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) local_unnamed_addr #5

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.value(metadata, metadata, metadata) #1

attributes #0 = { nofree nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable }
attributes #2 = { argmemonly nounwind }
attributes #3 = { nofree nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { argmemonly nofree nounwind readonly "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { nounwind }
attributes #8 = { nounwind readonly }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5}
!llvm.ident = !{!6}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, nameTableKind: None)
!1 = !DIFile(filename: "test-data/golden/golden-loop-merging/strlen_test2.c", directory: "/home/abakst/crucible/crux-llvm")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"clang version 9.0.0-2~ubuntu18.04.2 (tags/RELEASE_900/final)"}
!7 = distinct !DISubprogram(name: "test", scope: !1, file: !1, line: 22, type: !8, scopeLine: 22, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !18)
!8 = !DISubroutineType(types: !9)
!9 = !{null, !10, !13}
!10 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !11, size: 64)
!11 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !12)
!12 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!13 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint32_t", file: !14, line: 26, baseType: !15)
!14 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h", directory: "")
!15 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint32_t", file: !16, line: 41, baseType: !17)
!16 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types.h", directory: "")
!17 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!18 = !{!19, !20, !21}
!19 = !DILocalVariable(name: "string", arg: 1, scope: !7, file: !1, line: 22, type: !10)
!20 = !DILocalVariable(name: "length", arg: 2, scope: !7, file: !1, line: 22, type: !13)
!21 = !DILocalVariable(name: "i", scope: !7, file: !1, line: 23, type: !13)
!22 = !DILocation(line: 0, scope: !7)
!23 = !DILocation(line: 24, column: 16, scope: !24)
!24 = distinct !DILexicalBlock(scope: !25, file: !1, line: 24, column: 3)
!25 = distinct !DILexicalBlock(scope: !7, file: !1, line: 24, column: 3)
!26 = !DILocation(line: 24, column: 3, scope: !25)
!27 = !DILocation(line: 25, column: 5, scope: !28)
!28 = distinct !DILexicalBlock(scope: !24, file: !1, line: 24, column: 42)
!29 = !DILocation(line: 26, column: 67, scope: !28)
!30 = !DILocation(line: 26, column: 47, scope: !28)
!31 = !{!32, !32, i64 0}
!32 = !{!"omnipotent char", !33, i64 0}
!33 = !{!"Simple C/C++ TBAA"}
!34 = !DILocation(line: 26, column: 5, scope: !28)
!35 = !DILocation(line: 24, column: 38, scope: !24)
!36 = !DILocation(line: 24, column: 25, scope: !24)
!37 = distinct !{!37, !26, !38}
!38 = !DILocation(line: 27, column: 3, scope: !25)
!39 = !DILocation(line: 30, column: 1, scope: !7)
!40 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 32, type: !41, scopeLine: 32, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !44)
!41 = !DISubroutineType(types: !42)
!42 = !{!43}
!43 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!44 = !{!45, !49, !50}
!45 = !DILocalVariable(name: "str", scope: !40, file: !1, line: 33, type: !46)
!46 = !DICompositeType(tag: DW_TAG_array_type, baseType: !12, size: 800, elements: !47)
!47 = !{!48}
!48 = !DISubrange(count: 100)
!49 = !DILocalVariable(name: "i", scope: !40, file: !1, line: 35, type: !13)
!50 = !DILocalVariable(name: "length", scope: !40, file: !1, line: 40, type: !13)
!51 = !DILocation(line: 33, column: 3, scope: !40)
!52 = !DILocation(line: 33, column: 8, scope: !40)
!53 = !DILocation(line: 34, column: 3, scope: !40)
!54 = !DILocation(line: 35, column: 16, scope: !40)
!55 = !DILocation(line: 0, scope: !40)
!56 = !DILocation(line: 37, column: 3, scope: !40)
!57 = !DILocation(line: 38, column: 3, scope: !40)
!58 = !DILocation(line: 40, column: 21, scope: !40)
!59 = !DILocation(line: 41, column: 3, scope: !40)
!60 = !DILocation(line: 43, column: 3, scope: !40)
!61 = !DILocation(line: 46, column: 1, scope: !40)
!62 = !DILocation(line: 45, column: 3, scope: !40)
