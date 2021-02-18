; ModuleID = 'uint-cast.c'
source_filename = "uint-cast.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

%union.fb = type { i32 }

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @main() #0 !dbg !8 {
  %1 = alloca i32, align 4
  %2 = alloca %union.fb, align 4
  %3 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  call void @llvm.dbg.declare(metadata %union.fb* %2, metadata !12, metadata !DIExpression()), !dbg !26
  call void @llvm.dbg.declare(metadata i32* %3, metadata !27, metadata !DIExpression()), !dbg !28
  %4 = call i32 @__VERIFIER_nondet_uint(), !dbg !29
  store i32 %4, i32* %3, align 4, !dbg !28
  %5 = load i32, i32* %3, align 4, !dbg !30
  %6 = bitcast %union.fb* %2 to i32*, !dbg !31
  store i32 %5, i32* %6, align 4, !dbg !32
  %7 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !33
  %8 = getelementptr inbounds [4 x i8], [4 x i8]* %7, i64 0, i64 0, !dbg !34
  %9 = load i8, i8* %8, align 4, !dbg !34
  %10 = zext i8 %9 to i32, !dbg !34
  call void @crucible_print_uint32(i32 %10), !dbg !35
  %11 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !36
  %12 = getelementptr inbounds [4 x i8], [4 x i8]* %11, i64 0, i64 1, !dbg !37
  %13 = load i8, i8* %12, align 1, !dbg !37
  %14 = zext i8 %13 to i32, !dbg !37
  call void @crucible_print_uint32(i32 %14), !dbg !38
  %15 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !39
  %16 = getelementptr inbounds [4 x i8], [4 x i8]* %15, i64 0, i64 2, !dbg !40
  %17 = load i8, i8* %16, align 2, !dbg !40
  %18 = zext i8 %17 to i32, !dbg !40
  call void @crucible_print_uint32(i32 %18), !dbg !41
  %19 = bitcast %union.fb* %2 to [4 x i8]*, !dbg !42
  %20 = getelementptr inbounds [4 x i8], [4 x i8]* %19, i64 0, i64 3, !dbg !43
  %21 = load i8, i8* %20, align 1, !dbg !43
  %22 = zext i8 %21 to i32, !dbg !43
  call void @crucible_print_uint32(i32 %22), !dbg !44
  ret i32 0, !dbg !45
}

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

declare i32 @__VERIFIER_nondet_uint() #2

declare void @crucible_print_uint32(i32) #2

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6}
!llvm.ident = !{!7}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 7.1.0 (tags/RELEASE_710/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2)
!1 = !DIFile(filename: "uint-cast.c", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
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
!14 = !{!15, !19}
!15 = !DIDerivedType(tag: DW_TAG_member, name: "u", scope: !13, file: !1, line: 9, baseType: !16, size: 32)
!16 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint32_t", file: !17, line: 31, baseType: !18)
!17 = !DIFile(filename: "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/_types/_uint32_t.h", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
!18 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!19 = !DIDerivedType(tag: DW_TAG_member, name: "b", scope: !13, file: !1, line: 10, baseType: !20, size: 32)
!20 = !DICompositeType(tag: DW_TAG_array_type, baseType: !21, size: 32, elements: !24)
!21 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint8_t", file: !22, line: 31, baseType: !23)
!22 = !DIFile(filename: "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/_types/_uint8_t.h", directory: "/Users/rdockins/code/crucible/crux-llvm/test-data/golden")
!23 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!24 = !{!25}
!25 = !DISubrange(count: 4)
!26 = !DILocation(line: 14, column: 12, scope: !8)
!27 = !DILocalVariable(name: "x", scope: !8, file: !1, line: 15, type: !16)
!28 = !DILocation(line: 15, column: 12, scope: !8)
!29 = !DILocation(line: 15, column: 16, scope: !8)
!30 = !DILocation(line: 16, column: 9, scope: !8)
!31 = !DILocation(line: 16, column: 5, scope: !8)
!32 = !DILocation(line: 16, column: 7, scope: !8)
!33 = !DILocation(line: 18, column: 28, scope: !8)
!34 = !DILocation(line: 18, column: 26, scope: !8)
!35 = !DILocation(line: 18, column: 3, scope: !8)
!36 = !DILocation(line: 19, column: 28, scope: !8)
!37 = !DILocation(line: 19, column: 26, scope: !8)
!38 = !DILocation(line: 19, column: 3, scope: !8)
!39 = !DILocation(line: 20, column: 28, scope: !8)
!40 = !DILocation(line: 20, column: 26, scope: !8)
!41 = !DILocation(line: 20, column: 3, scope: !8)
!42 = !DILocation(line: 21, column: 28, scope: !8)
!43 = !DILocation(line: 21, column: 26, scope: !8)
!44 = !DILocation(line: 21, column: 3, scope: !8)
!45 = !DILocation(line: 23, column: 3, scope: !8)
