; ModuleID = 'T974.c'
source_filename = "T974.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [7 x i8] c"T974.c\00", align 1
@.str.1 = private unnamed_addr constant [6 x i8] c"smin1\00", align 1
@.str.2 = private unnamed_addr constant [6 x i8] c"smin2\00", align 1
@.str.3 = private unnamed_addr constant [6 x i8] c"smax1\00", align 1
@.str.4 = private unnamed_addr constant [6 x i8] c"smax2\00", align 1
@.str.5 = private unnamed_addr constant [6 x i8] c"umin1\00", align 1
@.str.6 = private unnamed_addr constant [6 x i8] c"umin2\00", align 1
@.str.7 = private unnamed_addr constant [6 x i8] c"umax1\00", align 1
@.str.8 = private unnamed_addr constant [6 x i8] c"umax2\00", align 1

declare i32 @llvm.smin.i32(i32, i32)
declare i32 @llvm.smax.i32(i32, i32)
declare i32 @llvm.umin.i32(i32, i32)
declare i32 @llvm.umax.i32(i32, i32)

; Function Attrs: norecurse nounwind readnone uwtable willreturn
define dso_local i32 @smin(i32 %x, i32 %y) local_unnamed_addr #0 {
entry:
  ; %cmp = icmp slt i32 %x, %y
  ; %cond = select i1 %cmp, i32 %x, i32 %y
  %cond = call i32 @llvm.smin.i32(i32 %x, i32 %y)
  ret i32 %cond
}

; Function Attrs: norecurse nounwind readnone uwtable willreturn
define dso_local i32 @smax(i32 %x, i32 %y) local_unnamed_addr #0 {
entry:
  ; %cmp = icmp sgt i32 %x, %y
  ; %cond = select i1 %cmp, i32 %x, i32 %y
  %cond = call i32 @llvm.smax.i32(i32 %x, i32 %y)
  ret i32 %cond
}

; Function Attrs: norecurse nounwind readnone uwtable willreturn
define dso_local i32 @umin(i32 %x, i32 %y) local_unnamed_addr #0 {
entry:
  ; %cmp = icmp ult i32 %x, %y
  ; %cond = select i1 %cmp, i32 %x, i32 %y
  %cond = call i32 @llvm.umin.i32(i32 %x, i32 %y)
  ret i32 %cond
}

; Function Attrs: norecurse nounwind readnone uwtable willreturn
define dso_local i32 @umax(i32 %x, i32 %y) local_unnamed_addr #0 {
entry:
  ; %cmp = icmp ugt i32 %x, %y
  ; %cond = select i1 %cmp, i32 %x, i32 %y
  %cond = call i32 @llvm.umax.i32(i32 %x, i32 %y)
  ret i32 %cond
}

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #1 {
entry:
  %call = call i32 @smin(i32 2, i32 3)
  %cmp = icmp eq i32 %call, 2
  %conv1 = zext i1 %cmp to i8
  call void @crucible_assert(i8 zeroext %conv1, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 26) #3
  %call2 = call i32 @smin(i32 3, i32 2)
  %cmp3 = icmp eq i32 %call2, 2
  %conv5 = zext i1 %cmp3 to i8
  call void @crucible_assert(i8 zeroext %conv5, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 27) #3
  %call6 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.1, i64 0, i64 0)) #3
  %call7 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i64 0, i64 0)) #3
  %cmp8 = icmp sle i32 %call6, %call7
  %conv10 = zext i1 %cmp8 to i8
  call void @crucible_assume(i8 zeroext %conv10, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 30) #3
  %call11 = call i32 @smin(i32 %call6, i32 %call7)
  %cmp12 = icmp eq i32 %call11, %call6
  %conv14 = zext i1 %cmp12 to i8
  call void @crucible_assert(i8 zeroext %conv14, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 31) #3
  %call15 = call i32 @smax(i32 2, i32 3)
  %cmp16 = icmp eq i32 %call15, 3
  %conv18 = zext i1 %cmp16 to i8
  call void @crucible_assert(i8 zeroext %conv18, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 34) #3
  %call19 = call i32 @smax(i32 3, i32 2)
  %cmp20 = icmp eq i32 %call19, 3
  %conv22 = zext i1 %cmp20 to i8
  call void @crucible_assert(i8 zeroext %conv22, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 35) #3
  %call23 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.3, i64 0, i64 0)) #3
  %call24 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.4, i64 0, i64 0)) #3
  %cmp25 = icmp sge i32 %call23, %call24
  %conv27 = zext i1 %cmp25 to i8
  call void @crucible_assume(i8 zeroext %conv27, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 38) #3
  %call28 = call i32 @smax(i32 %call23, i32 %call24)
  %cmp29 = icmp eq i32 %call28, %call23
  %conv31 = zext i1 %cmp29 to i8
  call void @crucible_assert(i8 zeroext %conv31, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 39) #3
  %call32 = call i32 @umin(i32 2, i32 3)
  %cmp33 = icmp eq i32 %call32, 2
  %conv35 = zext i1 %cmp33 to i8
  call void @crucible_assert(i8 zeroext %conv35, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 42) #3
  %call36 = call i32 @umin(i32 3, i32 2)
  %cmp37 = icmp eq i32 %call36, 2
  %conv39 = zext i1 %cmp37 to i8
  call void @crucible_assert(i8 zeroext %conv39, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 43) #3
  %call40 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.5, i64 0, i64 0)) #3
  %call41 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.6, i64 0, i64 0)) #3
  %cmp42 = icmp ule i32 %call40, %call41
  %conv44 = zext i1 %cmp42 to i8
  call void @crucible_assume(i8 zeroext %conv44, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 46) #3
  %call45 = call i32 @umin(i32 %call40, i32 %call41)
  %cmp46 = icmp eq i32 %call45, %call40
  %conv48 = zext i1 %cmp46 to i8
  call void @crucible_assert(i8 zeroext %conv48, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 47) #3
  %call49 = call i32 @umax(i32 2, i32 3)
  %cmp50 = icmp eq i32 %call49, 3
  %conv52 = zext i1 %cmp50 to i8
  call void @crucible_assert(i8 zeroext %conv52, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 50) #3
  %call53 = call i32 @umax(i32 3, i32 2)
  %cmp54 = icmp eq i32 %call53, 3
  %conv56 = zext i1 %cmp54 to i8
  call void @crucible_assert(i8 zeroext %conv56, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 51) #3
  %call57 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.7, i64 0, i64 0)) #3
  %call58 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.8, i64 0, i64 0)) #3
  %cmp59 = icmp uge i32 %call57, %call58
  %conv61 = zext i1 %cmp59 to i8
  call void @crucible_assume(i8 zeroext %conv61, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 54) #3
  %call62 = call i32 @umax(i32 %call57, i32 %call58)
  %cmp63 = icmp eq i32 %call62, %call57
  %conv65 = zext i1 %cmp63 to i8
  call void @crucible_assert(i8 zeroext %conv65, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 55) #3
  ret i32 0
}

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) local_unnamed_addr #2

declare dso_local i32 @crucible_int32_t(i8*) local_unnamed_addr #2

declare dso_local void @crucible_assume(i8 zeroext, i8*, i32) local_unnamed_addr #2

attributes #0 = { norecurse nounwind readnone uwtable willreturn "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind uwtable "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}
!llvm.commandline = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 12.0.1"}
!2 = !{!"/home/rscott/Software/clang+llvm-12.0.1/bin/clang-12 -fno-discard-value-names -frecord-command-line -S -D CRUCIBLE -emit-llvm -I ../../../c-src/includes -O1 T974.c -o T974.ll"}
