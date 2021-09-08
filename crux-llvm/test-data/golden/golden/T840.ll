; ModuleID = 'T840.c'
source_filename = "T840.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [4 x i8] c"x16\00", align 1
@.str.1 = private unnamed_addr constant [7 x i8] c"T840.c\00", align 1
@.str.2 = private unnamed_addr constant [4 x i8] c"x32\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x16 = alloca i16, align 2
  %x16_bswap = alloca i16, align 2
  %x32 = alloca i32, align 4
  %x32_bswap = alloca i32, align 4
  store i32 0, i32* %retval, align 4
  %call = call signext i16 @crucible_int16_t(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i64 0, i64 0))
  store i16 %call, i16* %x16, align 2
  %0 = load i16, i16* %x16, align 2
  %call1 = call zeroext i16 @__bswap_16(i16 zeroext %0)
  store i16 %call1, i16* %x16_bswap, align 2
  %1 = load i16, i16* %x16, align 2
  %call2 = call zeroext i16 @htons(i16 zeroext %1) #3
  %conv = zext i16 %call2 to i32
  %2 = load i16, i16* %x16_bswap, align 2
  %conv3 = zext i16 %2 to i32
  %cmp = icmp eq i32 %conv, %conv3
  %conv4 = zext i1 %cmp to i32
  %conv5 = trunc i32 %conv4 to i8
  call void @crucible_assert(i8 zeroext %conv5, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1, i64 0, i64 0), i32 9)
  %3 = load i16, i16* %x16, align 2
  %call6 = call zeroext i16 @ntohs(i16 zeroext %3) #3
  %conv7 = zext i16 %call6 to i32
  %4 = load i16, i16* %x16_bswap, align 2
  %conv8 = zext i16 %4 to i32
  %cmp9 = icmp eq i32 %conv7, %conv8
  %conv10 = zext i1 %cmp9 to i32
  %conv11 = trunc i32 %conv10 to i8
  call void @crucible_assert(i8 zeroext %conv11, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1, i64 0, i64 0), i32 10)
  %call12 = call i32 @crucible_int32_t(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.2, i64 0, i64 0))
  store i32 %call12, i32* %x32, align 4
  %5 = load i32, i32* %x32, align 4
  %call13 = call i32 @__bswap_32(i32 %5)
  store i32 %call13, i32* %x32_bswap, align 4
  %6 = load i32, i32* %x32, align 4
  %call14 = call i32 @htonl(i32 %6) #3
  %7 = load i32, i32* %x32_bswap, align 4
  %cmp15 = icmp eq i32 %call14, %7
  %conv16 = zext i1 %cmp15 to i32
  %conv17 = trunc i32 %conv16 to i8
  call void @crucible_assert(i8 zeroext %conv17, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1, i64 0, i64 0), i32 14)
  %8 = load i32, i32* %x32, align 4
  %call18 = call i32 @ntohl(i32 %8) #3
  %9 = load i32, i32* %x32_bswap, align 4
  %cmp19 = icmp eq i32 %call18, %9
  %conv20 = zext i1 %cmp19 to i32
  %conv21 = trunc i32 %conv20 to i8
  call void @crucible_assert(i8 zeroext %conv21, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1, i64 0, i64 0), i32 15)
  ret i32 0
}

declare dso_local signext i16 @crucible_int16_t(i8*) #1

; Function Attrs: noinline nounwind optnone uwtable
define internal zeroext i16 @__bswap_16(i16 zeroext %__bsx) #0 {
entry:
  %__bsx.addr = alloca i16, align 2
  store i16 %__bsx, i16* %__bsx.addr, align 2
  %0 = load i16, i16* %__bsx.addr, align 2
  %conv = zext i16 %0 to i32
  %shr = ashr i32 %conv, 8
  %and = and i32 %shr, 255
  %1 = load i16, i16* %__bsx.addr, align 2
  %conv1 = zext i16 %1 to i32
  %and2 = and i32 %conv1, 255
  %shl = shl i32 %and2, 8
  %or = or i32 %and, %shl
  %conv3 = trunc i32 %or to i16
  ret i16 %conv3
}

declare dso_local void @crucible_assert(i8 zeroext, i8*, i32) #1

; Function Attrs: nounwind readnone
declare dso_local zeroext i16 @htons(i16 zeroext) #2

; Function Attrs: nounwind readnone
declare dso_local zeroext i16 @ntohs(i16 zeroext) #2

declare dso_local i32 @crucible_int32_t(i8*) #1

; Function Attrs: noinline nounwind optnone uwtable
define internal i32 @__bswap_32(i32 %__bsx) #0 {
entry:
  %__bsx.addr = alloca i32, align 4
  store i32 %__bsx, i32* %__bsx.addr, align 4
  %0 = load i32, i32* %__bsx.addr, align 4
  %and = and i32 %0, -16777216
  %shr = lshr i32 %and, 24
  %1 = load i32, i32* %__bsx.addr, align 4
  %and1 = and i32 %1, 16711680
  %shr2 = lshr i32 %and1, 8
  %or = or i32 %shr, %shr2
  %2 = load i32, i32* %__bsx.addr, align 4
  %and3 = and i32 %2, 65280
  %shl = shl i32 %and3, 8
  %or4 = or i32 %or, %shl
  %3 = load i32, i32* %__bsx.addr, align 4
  %and5 = and i32 %3, 255
  %shl6 = shl i32 %and5, 24
  %or7 = or i32 %or4, %shl6
  ret i32 %or7
}

; Function Attrs: nounwind readnone
declare dso_local i32 @htonl(i32) #2

; Function Attrs: nounwind readnone
declare dso_local i32 @ntohl(i32) #2

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind readnone "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind readnone }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}
!llvm.commandline = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 10.0.0-4ubuntu1 "}
!2 = !{!"/usr/lib/llvm-10/bin/clang -fno-discard-value-names -frecord-command-line -S -D CRUCIBLE -emit-llvm -I ../../../c-src/includes -O0 T840.c -o T840.ll"}
