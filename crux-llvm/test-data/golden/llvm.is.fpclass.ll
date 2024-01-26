; ModuleID = 'llvm.is.fpclass.c'
source_filename = "llvm.is.fpclass.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [18 x i8] c"llvm.is.fpclass.c\00", align 1, !dbg !0

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 !dbg !18 {
  %1 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %2 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 1), !dbg !22
  %3 = zext i1 %2 to i8, !dbg !22
  call void @crucible_assert(i8 noundef zeroext %3, ptr noundef @.str, i32 noundef 19), !dbg !22
  %4 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 1), !dbg !23
  %5 = xor i1 %4, true, !dbg !23
  %6 = zext i1 %5 to i32, !dbg !23
  %7 = trunc i32 %6 to i8, !dbg !23
  call void @crucible_assert(i8 noundef zeroext %7, ptr noundef @.str, i32 noundef 20), !dbg !23
  %8 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 2), !dbg !24
  %9 = zext i1 %8 to i8, !dbg !24
  call void @crucible_assert(i8 noundef zeroext %9, ptr noundef @.str, i32 noundef 23), !dbg !24
  %10 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 2), !dbg !25
  %11 = xor i1 %10, true, !dbg !25
  %12 = zext i1 %11 to i32, !dbg !25
  %13 = trunc i32 %12 to i8, !dbg !25
  call void @crucible_assert(i8 noundef zeroext %13, ptr noundef @.str, i32 noundef 24), !dbg !25
  %14 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0xFFF0000000000000, i32 noundef 4), !dbg !26
  %15 = zext i1 %14 to i8, !dbg !26
  call void @crucible_assert(i8 noundef zeroext %15, ptr noundef @.str, i32 noundef 27), !dbg !26
  %16 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF0000000000000, i32 noundef 4), !dbg !27
  %17 = xor i1 %16, true, !dbg !27
  %18 = zext i1 %17 to i32, !dbg !27
  %19 = trunc i32 %18 to i8, !dbg !27
  call void @crucible_assert(i8 noundef zeroext %19, ptr noundef @.str, i32 noundef 28), !dbg !27
  %20 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 4), !dbg !28
  %21 = xor i1 %20, true, !dbg !28
  %22 = zext i1 %21 to i32, !dbg !28
  %23 = trunc i32 %22 to i8, !dbg !28
  call void @crucible_assert(i8 noundef zeroext %23, ptr noundef @.str, i32 noundef 29), !dbg !28
  %24 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 4), !dbg !29
  %25 = xor i1 %24, true, !dbg !29
  %26 = zext i1 %25 to i32, !dbg !29
  %27 = trunc i32 %26 to i8, !dbg !29
  call void @crucible_assert(i8 noundef zeroext %27, ptr noundef @.str, i32 noundef 30), !dbg !29
  %28 = call zeroext i1 @llvm.is.fpclass.f64(double noundef -4.250000e+01, i32 noundef 8), !dbg !30
  %29 = zext i1 %28 to i8, !dbg !30
  call void @crucible_assert(i8 noundef zeroext %29, ptr noundef @.str, i32 noundef 33), !dbg !30
  %30 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 8), !dbg !31
  %31 = xor i1 %30, true, !dbg !31
  %32 = zext i1 %31 to i32, !dbg !31
  %33 = trunc i32 %32 to i8, !dbg !31
  call void @crucible_assert(i8 noundef zeroext %33, ptr noundef @.str, i32 noundef 34), !dbg !31
  %34 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 8), !dbg !32
  %35 = xor i1 %34, true, !dbg !32
  %36 = zext i1 %35 to i32, !dbg !32
  %37 = trunc i32 %36 to i8, !dbg !32
  call void @crucible_assert(i8 noundef zeroext %37, ptr noundef @.str, i32 noundef 35), !dbg !32
  %38 = call zeroext i1 @llvm.is.fpclass.f64(double noundef -4.940660e-324, i32 noundef 16), !dbg !33
  %39 = zext i1 %38 to i8, !dbg !33
  call void @crucible_assert(i8 noundef zeroext %39, ptr noundef @.str, i32 noundef 38), !dbg !33
  %40 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.940660e-324, i32 noundef 16), !dbg !34
  %41 = xor i1 %40, true, !dbg !34
  %42 = zext i1 %41 to i32, !dbg !34
  %43 = trunc i32 %42 to i8, !dbg !34
  call void @crucible_assert(i8 noundef zeroext %43, ptr noundef @.str, i32 noundef 39), !dbg !34
  %44 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 16), !dbg !35
  %45 = xor i1 %44, true, !dbg !35
  %46 = zext i1 %45 to i32, !dbg !35
  %47 = trunc i32 %46 to i8, !dbg !35
  call void @crucible_assert(i8 noundef zeroext %47, ptr noundef @.str, i32 noundef 40), !dbg !35
  %48 = call zeroext i1 @llvm.is.fpclass.f64(double noundef -0.000000e+00, i32 noundef 32), !dbg !36
  %49 = zext i1 %48 to i8, !dbg !36
  call void @crucible_assert(i8 noundef zeroext %49, ptr noundef @.str, i32 noundef 43), !dbg !36
  %50 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0.000000e+00, i32 noundef 32), !dbg !37
  %51 = xor i1 %50, true, !dbg !37
  %52 = zext i1 %51 to i32, !dbg !37
  %53 = trunc i32 %52 to i8, !dbg !37
  call void @crucible_assert(i8 noundef zeroext %53, ptr noundef @.str, i32 noundef 44), !dbg !37
  %54 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 32), !dbg !38
  %55 = xor i1 %54, true, !dbg !38
  %56 = zext i1 %55 to i32, !dbg !38
  %57 = trunc i32 %56 to i8, !dbg !38
  call void @crucible_assert(i8 noundef zeroext %57, ptr noundef @.str, i32 noundef 45), !dbg !38
  %58 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 32), !dbg !39
  %59 = xor i1 %58, true, !dbg !39
  %60 = zext i1 %59 to i32, !dbg !39
  %61 = trunc i32 %60 to i8, !dbg !39
  call void @crucible_assert(i8 noundef zeroext %61, ptr noundef @.str, i32 noundef 46), !dbg !39
  %62 = call zeroext i1 @llvm.is.fpclass.f64(double noundef -0.000000e+00, i32 noundef 64), !dbg !40
  %63 = xor i1 %62, true, !dbg !40
  %64 = zext i1 %63 to i32, !dbg !40
  %65 = trunc i32 %64 to i8, !dbg !40
  call void @crucible_assert(i8 noundef zeroext %65, ptr noundef @.str, i32 noundef 49), !dbg !40
  %66 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0.000000e+00, i32 noundef 64), !dbg !41
  %67 = zext i1 %66 to i8, !dbg !41
  call void @crucible_assert(i8 noundef zeroext %67, ptr noundef @.str, i32 noundef 50), !dbg !41
  %68 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 64), !dbg !42
  %69 = xor i1 %68, true, !dbg !42
  %70 = zext i1 %69 to i32, !dbg !42
  %71 = trunc i32 %70 to i8, !dbg !42
  call void @crucible_assert(i8 noundef zeroext %71, ptr noundef @.str, i32 noundef 51), !dbg !42
  %72 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 64), !dbg !43
  %73 = xor i1 %72, true, !dbg !43
  %74 = zext i1 %73 to i32, !dbg !43
  %75 = trunc i32 %74 to i8, !dbg !43
  call void @crucible_assert(i8 noundef zeroext %75, ptr noundef @.str, i32 noundef 52), !dbg !43
  %76 = call zeroext i1 @llvm.is.fpclass.f64(double noundef -4.940660e-324, i32 noundef 128), !dbg !44
  %77 = xor i1 %76, true, !dbg !44
  %78 = zext i1 %77 to i32, !dbg !44
  %79 = trunc i32 %78 to i8, !dbg !44
  call void @crucible_assert(i8 noundef zeroext %79, ptr noundef @.str, i32 noundef 55), !dbg !44
  %80 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.940660e-324, i32 noundef 128), !dbg !45
  %81 = zext i1 %80 to i8, !dbg !45
  call void @crucible_assert(i8 noundef zeroext %81, ptr noundef @.str, i32 noundef 56), !dbg !45
  %82 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 128), !dbg !46
  %83 = xor i1 %82, true, !dbg !46
  %84 = zext i1 %83 to i32, !dbg !46
  %85 = trunc i32 %84 to i8, !dbg !46
  call void @crucible_assert(i8 noundef zeroext %85, ptr noundef @.str, i32 noundef 57), !dbg !46
  %86 = call zeroext i1 @llvm.is.fpclass.f64(double noundef -4.250000e+01, i32 noundef 256), !dbg !47
  %87 = xor i1 %86, true, !dbg !47
  %88 = zext i1 %87 to i32, !dbg !47
  %89 = trunc i32 %88 to i8, !dbg !47
  call void @crucible_assert(i8 noundef zeroext %89, ptr noundef @.str, i32 noundef 60), !dbg !47
  %90 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 256), !dbg !48
  %91 = zext i1 %90 to i8, !dbg !48
  call void @crucible_assert(i8 noundef zeroext %91, ptr noundef @.str, i32 noundef 61), !dbg !48
  %92 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 256), !dbg !49
  %93 = xor i1 %92, true, !dbg !49
  %94 = zext i1 %93 to i32, !dbg !49
  %95 = trunc i32 %94 to i8, !dbg !49
  call void @crucible_assert(i8 noundef zeroext %95, ptr noundef @.str, i32 noundef 62), !dbg !49
  %96 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0xFFF0000000000000, i32 noundef 512), !dbg !50
  %97 = xor i1 %96, true, !dbg !50
  %98 = zext i1 %97 to i32, !dbg !50
  %99 = trunc i32 %98 to i8, !dbg !50
  call void @crucible_assert(i8 noundef zeroext %99, ptr noundef @.str, i32 noundef 65), !dbg !50
  %100 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF0000000000000, i32 noundef 512), !dbg !51
  %101 = zext i1 %100 to i8, !dbg !51
  call void @crucible_assert(i8 noundef zeroext %101, ptr noundef @.str, i32 noundef 66), !dbg !51
  %102 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 512), !dbg !52
  %103 = xor i1 %102, true, !dbg !52
  %104 = zext i1 %103 to i32, !dbg !52
  %105 = trunc i32 %104 to i8, !dbg !52
  call void @crucible_assert(i8 noundef zeroext %105, ptr noundef @.str, i32 noundef 67), !dbg !52
  %106 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 512), !dbg !53
  %107 = xor i1 %106, true, !dbg !53
  %108 = zext i1 %107 to i32, !dbg !53
  %109 = trunc i32 %108 to i8, !dbg !53
  call void @crucible_assert(i8 noundef zeroext %109, ptr noundef @.str, i32 noundef 68), !dbg !53
  %110 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 3), !dbg !54
  %111 = zext i1 %110 to i8, !dbg !54
  call void @crucible_assert(i8 noundef zeroext %111, ptr noundef @.str, i32 noundef 73), !dbg !54
  %112 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 3), !dbg !55
  %113 = xor i1 %112, true, !dbg !55
  %114 = zext i1 %113 to i32, !dbg !55
  %115 = trunc i32 %114 to i8, !dbg !55
  call void @crucible_assert(i8 noundef zeroext %115, ptr noundef @.str, i32 noundef 74), !dbg !55
  %116 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0xFFF0000000000000, i32 noundef 516), !dbg !56
  %117 = zext i1 %116 to i8, !dbg !56
  call void @crucible_assert(i8 noundef zeroext %117, ptr noundef @.str, i32 noundef 77), !dbg !56
  %118 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF0000000000000, i32 noundef 516), !dbg !57
  %119 = zext i1 %118 to i8, !dbg !57
  call void @crucible_assert(i8 noundef zeroext %119, ptr noundef @.str, i32 noundef 78), !dbg !57
  %120 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 516), !dbg !58
  %121 = xor i1 %120, true, !dbg !58
  %122 = zext i1 %121 to i32, !dbg !58
  %123 = trunc i32 %122 to i8, !dbg !58
  call void @crucible_assert(i8 noundef zeroext %123, ptr noundef @.str, i32 noundef 79), !dbg !58
  %124 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 516), !dbg !59
  %125 = xor i1 %124, true, !dbg !59
  %126 = zext i1 %125 to i32, !dbg !59
  %127 = trunc i32 %126 to i8, !dbg !59
  call void @crucible_assert(i8 noundef zeroext %127, ptr noundef @.str, i32 noundef 80), !dbg !59
  %128 = call zeroext i1 @llvm.is.fpclass.f64(double noundef -4.250000e+01, i32 noundef 264), !dbg !60
  %129 = zext i1 %128 to i8, !dbg !60
  call void @crucible_assert(i8 noundef zeroext %129, ptr noundef @.str, i32 noundef 83), !dbg !60
  %130 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 264), !dbg !61
  %131 = zext i1 %130 to i8, !dbg !61
  call void @crucible_assert(i8 noundef zeroext %131, ptr noundef @.str, i32 noundef 84), !dbg !61
  %132 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 264), !dbg !62
  %133 = xor i1 %132, true, !dbg !62
  %134 = zext i1 %133 to i32, !dbg !62
  %135 = trunc i32 %134 to i8, !dbg !62
  call void @crucible_assert(i8 noundef zeroext %135, ptr noundef @.str, i32 noundef 85), !dbg !62
  %136 = call zeroext i1 @llvm.is.fpclass.f64(double noundef -4.940660e-324, i32 noundef 144), !dbg !63
  %137 = zext i1 %136 to i8, !dbg !63
  call void @crucible_assert(i8 noundef zeroext %137, ptr noundef @.str, i32 noundef 88), !dbg !63
  %138 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.940660e-324, i32 noundef 144), !dbg !64
  %139 = zext i1 %138 to i8, !dbg !64
  call void @crucible_assert(i8 noundef zeroext %139, ptr noundef @.str, i32 noundef 89), !dbg !64
  %140 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 144), !dbg !65
  %141 = xor i1 %140, true, !dbg !65
  %142 = zext i1 %141 to i32, !dbg !65
  %143 = trunc i32 %142 to i8, !dbg !65
  call void @crucible_assert(i8 noundef zeroext %143, ptr noundef @.str, i32 noundef 90), !dbg !65
  %144 = call zeroext i1 @llvm.is.fpclass.f64(double noundef -0.000000e+00, i32 noundef 96), !dbg !66
  %145 = zext i1 %144 to i8, !dbg !66
  call void @crucible_assert(i8 noundef zeroext %145, ptr noundef @.str, i32 noundef 93), !dbg !66
  %146 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0.000000e+00, i32 noundef 96), !dbg !67
  %147 = zext i1 %146 to i8, !dbg !67
  call void @crucible_assert(i8 noundef zeroext %147, ptr noundef @.str, i32 noundef 94), !dbg !67
  %148 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 4.250000e+01, i32 noundef 96), !dbg !68
  %149 = xor i1 %148, true, !dbg !68
  %150 = zext i1 %149 to i32, !dbg !68
  %151 = trunc i32 %150 to i8, !dbg !68
  call void @crucible_assert(i8 noundef zeroext %151, ptr noundef @.str, i32 noundef 95), !dbg !68
  %152 = call zeroext i1 @llvm.is.fpclass.f64(double noundef 0x7FF8000000000000, i32 noundef 96), !dbg !69
  %153 = xor i1 %152, true, !dbg !69
  %154 = zext i1 %153 to i32, !dbg !69
  %155 = trunc i32 %154 to i8, !dbg !69
  call void @crucible_assert(i8 noundef zeroext %155, ptr noundef @.str, i32 noundef 96), !dbg !69
  %156 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 1), !dbg !70
  %157 = zext i1 %156 to i8, !dbg !70
  call void @crucible_assert(i8 noundef zeroext %157, ptr noundef @.str, i32 noundef 103), !dbg !70
  %158 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 1), !dbg !71
  %159 = xor i1 %158, true, !dbg !71
  %160 = zext i1 %159 to i32, !dbg !71
  %161 = trunc i32 %160 to i8, !dbg !71
  call void @crucible_assert(i8 noundef zeroext %161, ptr noundef @.str, i32 noundef 104), !dbg !71
  %162 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 2), !dbg !72
  %163 = zext i1 %162 to i8, !dbg !72
  call void @crucible_assert(i8 noundef zeroext %163, ptr noundef @.str, i32 noundef 107), !dbg !72
  %164 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 2), !dbg !73
  %165 = xor i1 %164, true, !dbg !73
  %166 = zext i1 %165 to i32, !dbg !73
  %167 = trunc i32 %166 to i8, !dbg !73
  call void @crucible_assert(i8 noundef zeroext %167, ptr noundef @.str, i32 noundef 108), !dbg !73
  %168 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0xFFF0000000000000, i32 noundef 4), !dbg !74
  %169 = zext i1 %168 to i8, !dbg !74
  call void @crucible_assert(i8 noundef zeroext %169, ptr noundef @.str, i32 noundef 111), !dbg !74
  %170 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF0000000000000, i32 noundef 4), !dbg !75
  %171 = xor i1 %170, true, !dbg !75
  %172 = zext i1 %171 to i32, !dbg !75
  %173 = trunc i32 %172 to i8, !dbg !75
  call void @crucible_assert(i8 noundef zeroext %173, ptr noundef @.str, i32 noundef 112), !dbg !75
  %174 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 4), !dbg !76
  %175 = xor i1 %174, true, !dbg !76
  %176 = zext i1 %175 to i32, !dbg !76
  %177 = trunc i32 %176 to i8, !dbg !76
  call void @crucible_assert(i8 noundef zeroext %177, ptr noundef @.str, i32 noundef 113), !dbg !76
  %178 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 4), !dbg !77
  %179 = xor i1 %178, true, !dbg !77
  %180 = zext i1 %179 to i32, !dbg !77
  %181 = trunc i32 %180 to i8, !dbg !77
  call void @crucible_assert(i8 noundef zeroext %181, ptr noundef @.str, i32 noundef 114), !dbg !77
  %182 = call zeroext i1 @llvm.is.fpclass.f32(float noundef -4.250000e+01, i32 noundef 8), !dbg !78
  %183 = zext i1 %182 to i8, !dbg !78
  call void @crucible_assert(i8 noundef zeroext %183, ptr noundef @.str, i32 noundef 117), !dbg !78
  %184 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 8), !dbg !79
  %185 = xor i1 %184, true, !dbg !79
  %186 = zext i1 %185 to i32, !dbg !79
  %187 = trunc i32 %186 to i8, !dbg !79
  call void @crucible_assert(i8 noundef zeroext %187, ptr noundef @.str, i32 noundef 118), !dbg !79
  %188 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 8), !dbg !80
  %189 = xor i1 %188, true, !dbg !80
  %190 = zext i1 %189 to i32, !dbg !80
  %191 = trunc i32 %190 to i8, !dbg !80
  call void @crucible_assert(i8 noundef zeroext %191, ptr noundef @.str, i32 noundef 119), !dbg !80
  %192 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0xB6A0000000000000, i32 noundef 16), !dbg !81
  %193 = zext i1 %192 to i8, !dbg !81
  call void @crucible_assert(i8 noundef zeroext %193, ptr noundef @.str, i32 noundef 122), !dbg !81
  %194 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x36A0000000000000, i32 noundef 16), !dbg !82
  %195 = xor i1 %194, true, !dbg !82
  %196 = zext i1 %195 to i32, !dbg !82
  %197 = trunc i32 %196 to i8, !dbg !82
  call void @crucible_assert(i8 noundef zeroext %197, ptr noundef @.str, i32 noundef 123), !dbg !82
  %198 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 16), !dbg !83
  %199 = xor i1 %198, true, !dbg !83
  %200 = zext i1 %199 to i32, !dbg !83
  %201 = trunc i32 %200 to i8, !dbg !83
  call void @crucible_assert(i8 noundef zeroext %201, ptr noundef @.str, i32 noundef 124), !dbg !83
  %202 = call zeroext i1 @llvm.is.fpclass.f32(float noundef -0.000000e+00, i32 noundef 32), !dbg !84
  %203 = zext i1 %202 to i8, !dbg !84
  call void @crucible_assert(i8 noundef zeroext %203, ptr noundef @.str, i32 noundef 127), !dbg !84
  %204 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0.000000e+00, i32 noundef 32), !dbg !85
  %205 = xor i1 %204, true, !dbg !85
  %206 = zext i1 %205 to i32, !dbg !85
  %207 = trunc i32 %206 to i8, !dbg !85
  call void @crucible_assert(i8 noundef zeroext %207, ptr noundef @.str, i32 noundef 128), !dbg !85
  %208 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 32), !dbg !86
  %209 = xor i1 %208, true, !dbg !86
  %210 = zext i1 %209 to i32, !dbg !86
  %211 = trunc i32 %210 to i8, !dbg !86
  call void @crucible_assert(i8 noundef zeroext %211, ptr noundef @.str, i32 noundef 129), !dbg !86
  %212 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 32), !dbg !87
  %213 = xor i1 %212, true, !dbg !87
  %214 = zext i1 %213 to i32, !dbg !87
  %215 = trunc i32 %214 to i8, !dbg !87
  call void @crucible_assert(i8 noundef zeroext %215, ptr noundef @.str, i32 noundef 130), !dbg !87
  %216 = call zeroext i1 @llvm.is.fpclass.f32(float noundef -0.000000e+00, i32 noundef 64), !dbg !88
  %217 = xor i1 %216, true, !dbg !88
  %218 = zext i1 %217 to i32, !dbg !88
  %219 = trunc i32 %218 to i8, !dbg !88
  call void @crucible_assert(i8 noundef zeroext %219, ptr noundef @.str, i32 noundef 133), !dbg !88
  %220 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0.000000e+00, i32 noundef 64), !dbg !89
  %221 = zext i1 %220 to i8, !dbg !89
  call void @crucible_assert(i8 noundef zeroext %221, ptr noundef @.str, i32 noundef 134), !dbg !89
  %222 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 64), !dbg !90
  %223 = xor i1 %222, true, !dbg !90
  %224 = zext i1 %223 to i32, !dbg !90
  %225 = trunc i32 %224 to i8, !dbg !90
  call void @crucible_assert(i8 noundef zeroext %225, ptr noundef @.str, i32 noundef 135), !dbg !90
  %226 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 64), !dbg !91
  %227 = xor i1 %226, true, !dbg !91
  %228 = zext i1 %227 to i32, !dbg !91
  %229 = trunc i32 %228 to i8, !dbg !91
  call void @crucible_assert(i8 noundef zeroext %229, ptr noundef @.str, i32 noundef 136), !dbg !91
  %230 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0xB6A0000000000000, i32 noundef 128), !dbg !92
  %231 = xor i1 %230, true, !dbg !92
  %232 = zext i1 %231 to i32, !dbg !92
  %233 = trunc i32 %232 to i8, !dbg !92
  call void @crucible_assert(i8 noundef zeroext %233, ptr noundef @.str, i32 noundef 139), !dbg !92
  %234 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x36A0000000000000, i32 noundef 128), !dbg !93
  %235 = zext i1 %234 to i8, !dbg !93
  call void @crucible_assert(i8 noundef zeroext %235, ptr noundef @.str, i32 noundef 140), !dbg !93
  %236 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 128), !dbg !94
  %237 = xor i1 %236, true, !dbg !94
  %238 = zext i1 %237 to i32, !dbg !94
  %239 = trunc i32 %238 to i8, !dbg !94
  call void @crucible_assert(i8 noundef zeroext %239, ptr noundef @.str, i32 noundef 141), !dbg !94
  %240 = call zeroext i1 @llvm.is.fpclass.f32(float noundef -4.250000e+01, i32 noundef 256), !dbg !95
  %241 = xor i1 %240, true, !dbg !95
  %242 = zext i1 %241 to i32, !dbg !95
  %243 = trunc i32 %242 to i8, !dbg !95
  call void @crucible_assert(i8 noundef zeroext %243, ptr noundef @.str, i32 noundef 144), !dbg !95
  %244 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 256), !dbg !96
  %245 = zext i1 %244 to i8, !dbg !96
  call void @crucible_assert(i8 noundef zeroext %245, ptr noundef @.str, i32 noundef 145), !dbg !96
  %246 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 256), !dbg !97
  %247 = xor i1 %246, true, !dbg !97
  %248 = zext i1 %247 to i32, !dbg !97
  %249 = trunc i32 %248 to i8, !dbg !97
  call void @crucible_assert(i8 noundef zeroext %249, ptr noundef @.str, i32 noundef 146), !dbg !97
  %250 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0xFFF0000000000000, i32 noundef 512), !dbg !98
  %251 = xor i1 %250, true, !dbg !98
  %252 = zext i1 %251 to i32, !dbg !98
  %253 = trunc i32 %252 to i8, !dbg !98
  call void @crucible_assert(i8 noundef zeroext %253, ptr noundef @.str, i32 noundef 149), !dbg !98
  %254 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF0000000000000, i32 noundef 512), !dbg !99
  %255 = zext i1 %254 to i8, !dbg !99
  call void @crucible_assert(i8 noundef zeroext %255, ptr noundef @.str, i32 noundef 150), !dbg !99
  %256 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 512), !dbg !100
  %257 = xor i1 %256, true, !dbg !100
  %258 = zext i1 %257 to i32, !dbg !100
  %259 = trunc i32 %258 to i8, !dbg !100
  call void @crucible_assert(i8 noundef zeroext %259, ptr noundef @.str, i32 noundef 151), !dbg !100
  %260 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 512), !dbg !101
  %261 = xor i1 %260, true, !dbg !101
  %262 = zext i1 %261 to i32, !dbg !101
  %263 = trunc i32 %262 to i8, !dbg !101
  call void @crucible_assert(i8 noundef zeroext %263, ptr noundef @.str, i32 noundef 152), !dbg !101
  %264 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 3), !dbg !102
  %265 = zext i1 %264 to i8, !dbg !102
  call void @crucible_assert(i8 noundef zeroext %265, ptr noundef @.str, i32 noundef 157), !dbg !102
  %266 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 3), !dbg !103
  %267 = xor i1 %266, true, !dbg !103
  %268 = zext i1 %267 to i32, !dbg !103
  %269 = trunc i32 %268 to i8, !dbg !103
  call void @crucible_assert(i8 noundef zeroext %269, ptr noundef @.str, i32 noundef 158), !dbg !103
  %270 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0xFFF0000000000000, i32 noundef 516), !dbg !104
  %271 = zext i1 %270 to i8, !dbg !104
  call void @crucible_assert(i8 noundef zeroext %271, ptr noundef @.str, i32 noundef 161), !dbg !104
  %272 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF0000000000000, i32 noundef 516), !dbg !105
  %273 = zext i1 %272 to i8, !dbg !105
  call void @crucible_assert(i8 noundef zeroext %273, ptr noundef @.str, i32 noundef 162), !dbg !105
  %274 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 516), !dbg !106
  %275 = xor i1 %274, true, !dbg !106
  %276 = zext i1 %275 to i32, !dbg !106
  %277 = trunc i32 %276 to i8, !dbg !106
  call void @crucible_assert(i8 noundef zeroext %277, ptr noundef @.str, i32 noundef 163), !dbg !106
  %278 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 516), !dbg !107
  %279 = xor i1 %278, true, !dbg !107
  %280 = zext i1 %279 to i32, !dbg !107
  %281 = trunc i32 %280 to i8, !dbg !107
  call void @crucible_assert(i8 noundef zeroext %281, ptr noundef @.str, i32 noundef 164), !dbg !107
  %282 = call zeroext i1 @llvm.is.fpclass.f32(float noundef -4.250000e+01, i32 noundef 264), !dbg !108
  %283 = zext i1 %282 to i8, !dbg !108
  call void @crucible_assert(i8 noundef zeroext %283, ptr noundef @.str, i32 noundef 167), !dbg !108
  %284 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 264), !dbg !109
  %285 = zext i1 %284 to i8, !dbg !109
  call void @crucible_assert(i8 noundef zeroext %285, ptr noundef @.str, i32 noundef 168), !dbg !109
  %286 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 264), !dbg !110
  %287 = xor i1 %286, true, !dbg !110
  %288 = zext i1 %287 to i32, !dbg !110
  %289 = trunc i32 %288 to i8, !dbg !110
  call void @crucible_assert(i8 noundef zeroext %289, ptr noundef @.str, i32 noundef 169), !dbg !110
  %290 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0xB6A0000000000000, i32 noundef 144), !dbg !111
  %291 = zext i1 %290 to i8, !dbg !111
  call void @crucible_assert(i8 noundef zeroext %291, ptr noundef @.str, i32 noundef 172), !dbg !111
  %292 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x36A0000000000000, i32 noundef 144), !dbg !112
  %293 = zext i1 %292 to i8, !dbg !112
  call void @crucible_assert(i8 noundef zeroext %293, ptr noundef @.str, i32 noundef 173), !dbg !112
  %294 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 144), !dbg !113
  %295 = xor i1 %294, true, !dbg !113
  %296 = zext i1 %295 to i32, !dbg !113
  %297 = trunc i32 %296 to i8, !dbg !113
  call void @crucible_assert(i8 noundef zeroext %297, ptr noundef @.str, i32 noundef 174), !dbg !113
  %298 = call zeroext i1 @llvm.is.fpclass.f32(float noundef -0.000000e+00, i32 noundef 96), !dbg !114
  %299 = zext i1 %298 to i8, !dbg !114
  call void @crucible_assert(i8 noundef zeroext %299, ptr noundef @.str, i32 noundef 177), !dbg !114
  %300 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0.000000e+00, i32 noundef 96), !dbg !115
  %301 = zext i1 %300 to i8, !dbg !115
  call void @crucible_assert(i8 noundef zeroext %301, ptr noundef @.str, i32 noundef 178), !dbg !115
  %302 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 4.250000e+01, i32 noundef 96), !dbg !116
  %303 = xor i1 %302, true, !dbg !116
  %304 = zext i1 %303 to i32, !dbg !116
  %305 = trunc i32 %304 to i8, !dbg !116
  call void @crucible_assert(i8 noundef zeroext %305, ptr noundef @.str, i32 noundef 179), !dbg !116
  %306 = call zeroext i1 @llvm.is.fpclass.f32(float noundef 0x7FF8000000000000, i32 noundef 96), !dbg !117
  %307 = xor i1 %306, true, !dbg !117
  %308 = zext i1 %307 to i32, !dbg !117
  %309 = trunc i32 %308 to i8, !dbg !117
  call void @crucible_assert(i8 noundef zeroext %309, ptr noundef @.str, i32 noundef 180), !dbg !117
  ret i32 0, !dbg !118
}

declare void @crucible_assert(i8 noundef zeroext, ptr noundef, i32 noundef) #1

declare zeroext i1 @llvm.is.fpclass.f64(double noundef, i32 noundef) #1

declare zeroext i1 @llvm.is.fpclass.f32(float noundef, i32 noundef) #1

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!7}
!llvm.module.flags = !{!9, !10, !11, !12, !13, !14, !15}
!llvm.ident = !{!16}
!llvm.commandline = !{!17}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 19, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "llvm.is.fpclass.c", directory: "/home/ryanscott/Documents/Hacking/Haskell/crucible/crux-llvm/test-data/golden", checksumkind: CSK_MD5, checksum: "9160d01520ed9c0e94de44806b21e1b7")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 144, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 18)
!7 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 17.0.2 (++20230925113718+481358974fb0-1~exp1~20230925113734.45)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !8, splitDebugInlining: false, nameTableKind: None)
!8 = !{!0}
!9 = !{i32 7, !"Dwarf Version", i32 5}
!10 = !{i32 2, !"Debug Info Version", i32 3}
!11 = !{i32 1, !"wchar_size", i32 4}
!12 = !{i32 8, !"PIC Level", i32 2}
!13 = !{i32 7, !"PIE Level", i32 2}
!14 = !{i32 7, !"uwtable", i32 2}
!15 = !{i32 7, !"frame-pointer", i32 2}
!16 = !{!"Ubuntu clang version 17.0.2 (++20230925113718+481358974fb0-1~exp1~20230925113734.45)"}
!17 = !{!"/usr/lib/llvm-17/bin/clang -S -emit-llvm -g -I ../../c-src/includes -frecord-command-line llvm.is.fpclass.c"}
!18 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 13, type: !19, scopeLine: 13, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !7)
!19 = !DISubroutineType(types: !20)
!20 = !{!21}
!21 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!22 = !DILocation(line: 19, column: 3, scope: !18)
!23 = !DILocation(line: 20, column: 3, scope: !18)
!24 = !DILocation(line: 23, column: 3, scope: !18)
!25 = !DILocation(line: 24, column: 3, scope: !18)
!26 = !DILocation(line: 27, column: 3, scope: !18)
!27 = !DILocation(line: 28, column: 3, scope: !18)
!28 = !DILocation(line: 29, column: 3, scope: !18)
!29 = !DILocation(line: 30, column: 3, scope: !18)
!30 = !DILocation(line: 33, column: 3, scope: !18)
!31 = !DILocation(line: 34, column: 3, scope: !18)
!32 = !DILocation(line: 35, column: 3, scope: !18)
!33 = !DILocation(line: 38, column: 3, scope: !18)
!34 = !DILocation(line: 39, column: 3, scope: !18)
!35 = !DILocation(line: 40, column: 3, scope: !18)
!36 = !DILocation(line: 43, column: 3, scope: !18)
!37 = !DILocation(line: 44, column: 3, scope: !18)
!38 = !DILocation(line: 45, column: 3, scope: !18)
!39 = !DILocation(line: 46, column: 3, scope: !18)
!40 = !DILocation(line: 49, column: 3, scope: !18)
!41 = !DILocation(line: 50, column: 3, scope: !18)
!42 = !DILocation(line: 51, column: 3, scope: !18)
!43 = !DILocation(line: 52, column: 3, scope: !18)
!44 = !DILocation(line: 55, column: 3, scope: !18)
!45 = !DILocation(line: 56, column: 3, scope: !18)
!46 = !DILocation(line: 57, column: 3, scope: !18)
!47 = !DILocation(line: 60, column: 3, scope: !18)
!48 = !DILocation(line: 61, column: 3, scope: !18)
!49 = !DILocation(line: 62, column: 3, scope: !18)
!50 = !DILocation(line: 65, column: 3, scope: !18)
!51 = !DILocation(line: 66, column: 3, scope: !18)
!52 = !DILocation(line: 67, column: 3, scope: !18)
!53 = !DILocation(line: 68, column: 3, scope: !18)
!54 = !DILocation(line: 73, column: 3, scope: !18)
!55 = !DILocation(line: 74, column: 3, scope: !18)
!56 = !DILocation(line: 77, column: 3, scope: !18)
!57 = !DILocation(line: 78, column: 3, scope: !18)
!58 = !DILocation(line: 79, column: 3, scope: !18)
!59 = !DILocation(line: 80, column: 3, scope: !18)
!60 = !DILocation(line: 83, column: 3, scope: !18)
!61 = !DILocation(line: 84, column: 3, scope: !18)
!62 = !DILocation(line: 85, column: 3, scope: !18)
!63 = !DILocation(line: 88, column: 3, scope: !18)
!64 = !DILocation(line: 89, column: 3, scope: !18)
!65 = !DILocation(line: 90, column: 3, scope: !18)
!66 = !DILocation(line: 93, column: 3, scope: !18)
!67 = !DILocation(line: 94, column: 3, scope: !18)
!68 = !DILocation(line: 95, column: 3, scope: !18)
!69 = !DILocation(line: 96, column: 3, scope: !18)
!70 = !DILocation(line: 103, column: 3, scope: !18)
!71 = !DILocation(line: 104, column: 3, scope: !18)
!72 = !DILocation(line: 107, column: 3, scope: !18)
!73 = !DILocation(line: 108, column: 3, scope: !18)
!74 = !DILocation(line: 111, column: 3, scope: !18)
!75 = !DILocation(line: 112, column: 3, scope: !18)
!76 = !DILocation(line: 113, column: 3, scope: !18)
!77 = !DILocation(line: 114, column: 3, scope: !18)
!78 = !DILocation(line: 117, column: 3, scope: !18)
!79 = !DILocation(line: 118, column: 3, scope: !18)
!80 = !DILocation(line: 119, column: 3, scope: !18)
!81 = !DILocation(line: 122, column: 3, scope: !18)
!82 = !DILocation(line: 123, column: 3, scope: !18)
!83 = !DILocation(line: 124, column: 3, scope: !18)
!84 = !DILocation(line: 127, column: 3, scope: !18)
!85 = !DILocation(line: 128, column: 3, scope: !18)
!86 = !DILocation(line: 129, column: 3, scope: !18)
!87 = !DILocation(line: 130, column: 3, scope: !18)
!88 = !DILocation(line: 133, column: 3, scope: !18)
!89 = !DILocation(line: 134, column: 3, scope: !18)
!90 = !DILocation(line: 135, column: 3, scope: !18)
!91 = !DILocation(line: 136, column: 3, scope: !18)
!92 = !DILocation(line: 139, column: 3, scope: !18)
!93 = !DILocation(line: 140, column: 3, scope: !18)
!94 = !DILocation(line: 141, column: 3, scope: !18)
!95 = !DILocation(line: 144, column: 3, scope: !18)
!96 = !DILocation(line: 145, column: 3, scope: !18)
!97 = !DILocation(line: 146, column: 3, scope: !18)
!98 = !DILocation(line: 149, column: 3, scope: !18)
!99 = !DILocation(line: 150, column: 3, scope: !18)
!100 = !DILocation(line: 151, column: 3, scope: !18)
!101 = !DILocation(line: 152, column: 3, scope: !18)
!102 = !DILocation(line: 157, column: 3, scope: !18)
!103 = !DILocation(line: 158, column: 3, scope: !18)
!104 = !DILocation(line: 161, column: 3, scope: !18)
!105 = !DILocation(line: 162, column: 3, scope: !18)
!106 = !DILocation(line: 163, column: 3, scope: !18)
!107 = !DILocation(line: 164, column: 3, scope: !18)
!108 = !DILocation(line: 167, column: 3, scope: !18)
!109 = !DILocation(line: 168, column: 3, scope: !18)
!110 = !DILocation(line: 169, column: 3, scope: !18)
!111 = !DILocation(line: 172, column: 3, scope: !18)
!112 = !DILocation(line: 173, column: 3, scope: !18)
!113 = !DILocation(line: 174, column: 3, scope: !18)
!114 = !DILocation(line: 177, column: 3, scope: !18)
!115 = !DILocation(line: 178, column: 3, scope: !18)
!116 = !DILocation(line: 179, column: 3, scope: !18)
!117 = !DILocation(line: 180, column: 3, scope: !18)
!118 = !DILocation(line: 182, column: 3, scope: !18)
