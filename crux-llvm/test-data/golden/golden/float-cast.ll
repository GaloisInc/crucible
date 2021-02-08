; ModuleID = 'float-cast.c'
source_filename = "float-cast.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

%union.fb = type { float }

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @main() #0 !dbg !8 {
  %1 = alloca i32, align 4
  %2 = alloca %union.fb, align 4
  %3 = alloca float, align 4
  store i32 0, i32* %1, align 4
  call void @llvm.dbg.declare(metadata %union.fb* %2, metadata !12, metadata !DIExpression()), !dbg !24
  call void @llvm.dbg.declare(metadata float* %3, metadata !25, metadata !DIExpression()), !dbg !26
  %4 = call float @__VERIFIER_nondet_float(), !dbg !27
  store float %4, float* %3, align 4, !dbg !26
  %5 = load float, float* %3, align 4, !dbg !28
  %6 = bitcast %union.fb* %2 to float*, !dbg !29
  store float %5, float* %6, align 4, !dbg !30
  %7 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !31
  %8 = getelementptr inbounds [4 x i8], [4 x i8]* %7, i64 0, i64 0, !dbg !32
  %9 = load i8, i8* %8, align 4, !dbg !32
  %10 = zext i8 %9 to i32, !dbg !32
  call void @crucible_print_uint32(i32 %10), !dbg !33
  %11 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !34
  %12 = getelementptr inbounds [4 x i8], [4 x i8]* %11, i64 0, i64 1, !dbg !35
  %13 = load i8, i8* %12, align 1, !dbg !35
  %14 = zext i8 %13 to i32, !dbg !35
  call void @crucible_print_uint32(i32 %14), !dbg !36
  %15 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !37
  %16 = getelementptr inbounds [4 x i8], [4 x i8]* %15, i64 0, i64 2, !dbg !38
  %17 = load i8, i8* %16, align 2, !dbg !38
  %18 = zext i8 %17 to i32, !dbg !38
  call void @crucible_print_uint32(i32 %18), !dbg !39
  %19 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !40
  %20 = getelementptr inbounds [4 x i8], [4 x i8]* %19, i64 0, i64 3, !dbg !41
  %21 = load i8, i8* %20, align 1, !dbg !41
  %22 = zext i8 %21 to i32, !dbg !41
  call void @crucible_print_uint32(i32 %22), !dbg !42
  ret i32 0, !dbg !43
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
!1 = !DIFile(filename: "float-cast.c", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{!"clang version 7.1.0 (tags/RELEASE_710/final)"}
!8 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 13, type: !9, isLocal: false, isDefinition: true, scopeLine: 13, isOptimized: false, unit: !0, retainedNodes: !2)
!9 = !DISubroutineType(types: !10)
!10 = !{!11}
!11 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!12 = !DILocalVariable(name: "u", scope: !8, file: !1, line: 14, type: !13)
!13 = distinct !DICompositeType(tag: DW_TAG_union_type, name: "fb", file: !1, line: 8, size: 32, elements: !14)
!14 = !{!15, !17}
!15 = !DIDerivedType(tag: DW_TAG_member, name: "f", scope: !13, file: !1, line: 9, baseType: !16, size: 32)
!16 = !DIBasicType(name: "float", size: 32, encoding: DW_ATE_float)
!17 = !DIDerivedType(tag: DW_TAG_member, name: "b", scope: !13, file: !1, line: 10, baseType: !18, size: 32)
!18 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 32, elements: !22)
!19 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint8_t", file: !20, line: 31, baseType: !21)
!20 = !DIFile(filename: "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/_types/_uint8_t.h", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
!21 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!22 = !{!23}
!23 = !DISubrange(count: 4)
!24 = !DILocation(line: 14, column: 12, scope: !8)
!25 = !DILocalVariable(name: "f", scope: !8, file: !1, line: 15, type: !16)
!26 = !DILocation(line: 15, column: 9, scope: !8)
!27 = !DILocation(line: 15, column: 13, scope: !8)
!28 = !DILocation(line: 16, column: 9, scope: !8)
!29 = !DILocation(line: 16, column: 5, scope: !8)
!30 = !DILocation(line: 16, column: 7, scope: !8)
!31 = !DILocation(line: 18, column: 28, scope: !8)
!32 = !DILocation(line: 18, column: 26, scope: !8)
!33 = !DILocation(line: 18, column: 3, scope: !8)
!34 = !DILocation(line: 19, column: 28, scope: !8)
!35 = !DILocation(line: 19, column: 26, scope: !8)
!36 = !DILocation(line: 19, column: 3, scope: !8)
!37 = !DILocation(line: 20, column: 28, scope: !8)
!38 = !DILocation(line: 20, column: 26, scope: !8)
!39 = !DILocation(line: 20, column: 3, scope: !8)
!40 = !DILocation(line: 21, column: 28, scope: !8)
!41 = !DILocation(line: 21, column: 26, scope: !8)
!42 = !DILocation(line: 21, column: 3, scope: !8)
!43 = !DILocation(line: 23, column: 3, scope: !8)
