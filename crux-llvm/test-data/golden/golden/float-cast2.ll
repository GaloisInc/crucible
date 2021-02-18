; ModuleID = 'float-cast2.c'
source_filename = "float-cast2.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

%union.fb = type { float }

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @main() #0 !dbg !8 {
  %1 = alloca i32, align 4
  %2 = alloca %union.fb, align 4
  %3 = alloca float, align 4
  %4 = alloca %union.fb, align 4
  store i32 0, i32* %1, align 4
  call void @llvm.dbg.declare(metadata %union.fb* %2, metadata !12, metadata !DIExpression()), !dbg !24
  call void @llvm.dbg.declare(metadata float* %3, metadata !25, metadata !DIExpression()), !dbg !26
  %5 = call float @__VERIFIER_nondet_float(), !dbg !27
  store float %5, float* %3, align 4, !dbg !26
  %6 = load float, float* %3, align 4, !dbg !28
  %7 = bitcast %union.fb* %2 to float*, !dbg !29
  store float %6, float* %7, align 4, !dbg !30
  call void @llvm.dbg.declare(metadata %union.fb* %4, metadata !31, metadata !DIExpression()), !dbg !32
  %8 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !33
  %9 = getelementptr inbounds [4 x i8], [4 x i8]* %8, i64 0, i64 0, !dbg !34
  %10 = load i8, i8* %9, align 4, !dbg !34
  %11 = bitcast %union.fb* %4 to [4 x i8]*, !dbg !35
  %12 = getelementptr inbounds [4 x i8], [4 x i8]* %11, i64 0, i64 0, !dbg !36
  store i8 %10, i8* %12, align 4, !dbg !37
  %13 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !38
  %14 = getelementptr inbounds [4 x i8], [4 x i8]* %13, i64 0, i64 1, !dbg !39
  %15 = load i8, i8* %14, align 1, !dbg !39
  %16 = bitcast %union.fb* %4 to [4 x i8]*, !dbg !40
  %17 = getelementptr inbounds [4 x i8], [4 x i8]* %16, i64 0, i64 1, !dbg !41
  store i8 %15, i8* %17, align 1, !dbg !42
  %18 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !43
  %19 = getelementptr inbounds [4 x i8], [4 x i8]* %18, i64 0, i64 2, !dbg !44
  %20 = load i8, i8* %19, align 2, !dbg !44
  %21 = bitcast %union.fb* %4 to [4 x i8]*, !dbg !45
  %22 = getelementptr inbounds [4 x i8], [4 x i8]* %21, i64 0, i64 2, !dbg !46
  store i8 %20, i8* %22, align 2, !dbg !47
  %23 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !48
  %24 = getelementptr inbounds [4 x i8], [4 x i8]* %23, i64 0, i64 3, !dbg !49
  %25 = load i8, i8* %24, align 1, !dbg !49
  %26 = bitcast %union.fb* %4 to [4 x i8]*, !dbg !50
  %27 = getelementptr inbounds [4 x i8], [4 x i8]* %26, i64 0, i64 3, !dbg !51
  store i8 %25, i8* %27, align 1, !dbg !52
  %28 = bitcast %union.fb* %2 to float*, !dbg !53
  %29 = load float, float* %28, align 4, !dbg !53
  %30 = bitcast %union.fb* %4 to float*, !dbg !54
  %31 = load float, float* %30, align 4, !dbg !54
  %32 = fcmp oeq float %29, %31, !dbg !55
  %33 = zext i1 %32 to i32, !dbg !55
  call void @crucible_print_uint32(i32 %33), !dbg !56
  ret i32 0, !dbg !57
}

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

declare float @__VERIFIER_nondet_float() #2

declare void @crucible_print_uint32(i32) #2

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6}
!llvm.ident = !{!7}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 7.1.0 (tags/RELEASE_710/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2)
!1 = !DIFile(filename: "float-cast2.c", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{!"clang version 7.1.0 (tags/RELEASE_710/final)"}
!8 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 11, type: !9, isLocal: false, isDefinition: true, scopeLine: 11, isOptimized: false, unit: !0, retainedNodes: !2)
!9 = !DISubroutineType(types: !10)
!10 = !{!11}
!11 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!12 = !DILocalVariable(name: "u", scope: !8, file: !1, line: 12, type: !13)
!13 = distinct !DICompositeType(tag: DW_TAG_union_type, name: "fb", file: !1, line: 6, size: 32, elements: !14)
!14 = !{!15, !17}
!15 = !DIDerivedType(tag: DW_TAG_member, name: "f", scope: !13, file: !1, line: 7, baseType: !16, size: 32)
!16 = !DIBasicType(name: "float", size: 32, encoding: DW_ATE_float)
!17 = !DIDerivedType(tag: DW_TAG_member, name: "b", scope: !13, file: !1, line: 8, baseType: !18, size: 32)
!18 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 32, elements: !22)
!19 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint8_t", file: !20, line: 31, baseType: !21)
!20 = !DIFile(filename: "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/_types/_uint8_t.h", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
!21 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!22 = !{!23}
!23 = !DISubrange(count: 4)
!24 = !DILocation(line: 12, column: 12, scope: !8)
!25 = !DILocalVariable(name: "f", scope: !8, file: !1, line: 13, type: !16)
!26 = !DILocation(line: 13, column: 9, scope: !8)
!27 = !DILocation(line: 13, column: 13, scope: !8)
!28 = !DILocation(line: 14, column: 9, scope: !8)
!29 = !DILocation(line: 14, column: 5, scope: !8)
!30 = !DILocation(line: 14, column: 7, scope: !8)
!31 = !DILocalVariable(name: "u2", scope: !8, file: !1, line: 16, type: !13)
!32 = !DILocation(line: 16, column: 12, scope: !8)
!33 = !DILocation(line: 18, column: 15, scope: !8)
!34 = !DILocation(line: 18, column: 13, scope: !8)
!35 = !DILocation(line: 18, column: 6, scope: !8)
!36 = !DILocation(line: 18, column: 3, scope: !8)
!37 = !DILocation(line: 18, column: 11, scope: !8)
!38 = !DILocation(line: 19, column: 15, scope: !8)
!39 = !DILocation(line: 19, column: 13, scope: !8)
!40 = !DILocation(line: 19, column: 6, scope: !8)
!41 = !DILocation(line: 19, column: 3, scope: !8)
!42 = !DILocation(line: 19, column: 11, scope: !8)
!43 = !DILocation(line: 20, column: 15, scope: !8)
!44 = !DILocation(line: 20, column: 13, scope: !8)
!45 = !DILocation(line: 20, column: 6, scope: !8)
!46 = !DILocation(line: 20, column: 3, scope: !8)
!47 = !DILocation(line: 20, column: 11, scope: !8)
!48 = !DILocation(line: 21, column: 15, scope: !8)
!49 = !DILocation(line: 21, column: 13, scope: !8)
!50 = !DILocation(line: 21, column: 6, scope: !8)
!51 = !DILocation(line: 21, column: 3, scope: !8)
!52 = !DILocation(line: 21, column: 11, scope: !8)
!53 = !DILocation(line: 23, column: 28, scope: !8)
!54 = !DILocation(line: 23, column: 36, scope: !8)
!55 = !DILocation(line: 23, column: 30, scope: !8)
!56 = !DILocation(line: 23, column: 3, scope: !8)
!57 = !DILocation(line: 25, column: 3, scope: !8)
