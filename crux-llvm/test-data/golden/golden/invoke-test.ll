; ModuleID = 'test.7rcbfp3g-cgu.0'
source_filename = "test.7rcbfp3g-cgu.0"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-darwin"

%"core::fmt::Formatter" = type { [0 x i64], { i64, i64 }, [0 x i64], { i64, i64 }, [0 x i64], { {}*, [3 x i64]* }, [0 x i64], { i64*, i64* }, [0 x i64], { [0 x { i8*, i8* }]*, i64 }, [0 x i32], i32, [0 x i32], i32, [0 x i8], i8, [7 x i8] }
%"core::fmt::Void" = type { [0 x i8], {}, [0 x i8], %"core::marker::PhantomData<*mut core::ops::function::Fn<(), Output=()>>", [0 x i8] }
%"core::marker::PhantomData<*mut core::ops::function::Fn<(), Output=()>>" = type {}
%"core::fmt::Arguments" = type { [0 x i64], { [0 x { [0 x i8]*, i64 }]*, i64 }, [0 x i64], { i64*, i64 }, [0 x i64], { [0 x { i8*, i8* }]*, i64 }, [0 x i64] }
%"core::fmt::rt::v1::Argument" = type { [0 x i64], { i64, i64 }, [0 x i64], %"core::fmt::rt::v1::FormatSpec", [0 x i64] }
%"core::fmt::rt::v1::FormatSpec" = type { [0 x i64], { i64, i64 }, [0 x i64], { i64, i64 }, [0 x i32], i32, [0 x i32], i32, [0 x i8], i8, [7 x i8] }
%"core::slice::Repr<[i32; 4]>" = type { [2 x i64] }
%"core::slice::Repr<i32>" = type { [2 x i64] }
%"core::marker::PhantomData<&mut i32>" = type {}
%"core::marker::PhantomData<&mut [i32; 4]>" = type {}
%BI = type { [0 x i32], [2 x [4 x i32]], [0 x i32] }
%"unwind::libunwind::_Unwind_Exception" = type { [0 x i64], i64, [0 x i64], void (i32, %"unwind::libunwind::_Unwind_Exception"*)*, [0 x i64], [6 x i64], [0 x i64] }
%"unwind::libunwind::_Unwind_Context" = type { [0 x i8] }

@vtable.0 = private unnamed_addr constant { void (i8**)*, i64, i64, i32 (i8**)*, i32 (i8**)*, i32 (i8**)* } { void (i8**)* @_ZN4core3ptr18real_drop_in_place17h96afe4d514bb3c38E, i64 8, i64 8, i32 (i8**)* @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h6e1c450892b1f754E", i32 (i8**)* @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h6e1c450892b1f754E", i32 (i8**)* @"_ZN4core3ops8function6FnOnce9call_once32_$u7b$$u7b$vtable.shim$u7d$$u7d$17hbfe54a791614f945E" }, align 8
@0 = private unnamed_addr constant <{ [0 x i8] }> zeroinitializer, align 1
@1 = private unnamed_addr constant <{ [1 x i8] }> <{ [1 x i8] c"\0A" }>, align 1
@2 = private unnamed_addr constant <{ i8*, [8 x i8], i8*, [8 x i8] }> <{ i8* getelementptr inbounds (<{ [0 x i8] }>, <{ [0 x i8] }>* @0, i32 0, i32 0, i32 0), [8 x i8] zeroinitializer, i8* getelementptr inbounds (<{ [1 x i8] }>, <{ [1 x i8] }>* @1, i32 0, i32 0, i32 0), [8 x i8] c"\01\00\00\00\00\00\00\00" }>, align 8
@3 = private unnamed_addr constant <{ [64 x i8] }> <{ [64 x i8] c"\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00 \00\00\00\00\00\00\00\03\00\00\00\00\00\00\00" }>, align 8

; std::rt::lang_start
; Function Attrs: uwtable
define hidden i64 @_ZN3std2rt10lang_start17h4f32aa1279b9079fE(void ()* nonnull %main, i64 %argc, i8** %argv) unnamed_addr #0 {
start:
  %_7 = alloca i8*, align 8
  %0 = bitcast i8** %_7 to void ()**
  store void ()* %main, void ()** %0, align 8
  %1 = bitcast i8** %_7 to {}*
; call std::rt::lang_start_internal
  %2 = call i64 @_ZN3std2rt19lang_start_internal17h3dc68cf5532522d7E({}* nonnull align 1 %1, [3 x i64]* noalias readonly align 8 dereferenceable(24) bitcast ({ void (i8**)*, i64, i64, i32 (i8**)*, i32 (i8**)*, i32 (i8**)* }* @vtable.0 to [3 x i64]*), i64 %argc, i8** %argv)
  br label %bb1

bb1:                                              ; preds = %start
  ret i64 %2
}

; std::rt::lang_start::{{closure}}
; Function Attrs: uwtable
define internal i32 @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h6e1c450892b1f754E"(i8** noalias readonly align 8 dereferenceable(8) %arg0) unnamed_addr #0 {
start:
  %0 = bitcast i8** %arg0 to void ()**
  %1 = load void ()*, void ()** %0, align 8, !nonnull !1
  call void %1()
  br label %bb1

bb1:                                              ; preds = %start
; call <() as std::process::Termination>::report
  %2 = call i32 @"_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17ha97fdaad4e15facaE"()
  br label %bb2

bb2:                                              ; preds = %bb1
  ret i32 %2
}

; std::sys::unix::process::process_common::ExitCode::as_i32
; Function Attrs: inlinehint uwtable
define internal i32 @_ZN3std3sys4unix7process14process_common8ExitCode6as_i3217h131bd83b3a6fff4bE(i8* noalias readonly align 1 dereferenceable(1) %self) unnamed_addr #1 {
start:
  %0 = load i8, i8* %self, align 1
  %1 = zext i8 %0 to i32
  ret i32 %1
}

; core::fmt::ArgumentV1::new
; Function Attrs: uwtable
define internal { i8*, i8* } @_ZN4core3fmt10ArgumentV13new17h0af350dc6d28844eE(i32* noalias readonly align 4 dereferenceable(4) %x, i1 (i32*, %"core::fmt::Formatter"*)* nonnull %f) unnamed_addr #0 {
start:
  %transmute_temp1 = alloca %"core::fmt::Void"*, align 8
  %transmute_temp = alloca i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)*, align 8
  %_0 = alloca { i8*, i8* }, align 8
  %0 = bitcast i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)** %transmute_temp to i1 (i32*, %"core::fmt::Formatter"*)**
  store i1 (i32*, %"core::fmt::Formatter"*)* %f, i1 (i32*, %"core::fmt::Formatter"*)** %0, align 8
  %1 = load i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)*, i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)** %transmute_temp, align 8, !nonnull !1
  br label %bb1

bb1:                                              ; preds = %start
  %2 = bitcast %"core::fmt::Void"** %transmute_temp1 to i32**
  store i32* %x, i32** %2, align 8
  %3 = load %"core::fmt::Void"*, %"core::fmt::Void"** %transmute_temp1, align 8, !nonnull !1
  br label %bb2

bb2:                                              ; preds = %bb1
  %4 = bitcast { i8*, i8* }* %_0 to %"core::fmt::Void"**
  store %"core::fmt::Void"* %3, %"core::fmt::Void"** %4, align 8
  %5 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %_0, i32 0, i32 1
  %6 = bitcast i8** %5 to i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)**
  store i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)* %1, i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)** %6, align 8
  %7 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %_0, i32 0, i32 0
  %8 = load i8*, i8** %7, align 8, !nonnull !1
  %9 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %_0, i32 0, i32 1
  %10 = load i8*, i8** %9, align 8, !nonnull !1
  %11 = insertvalue { i8*, i8* } undef, i8* %8, 0
  %12 = insertvalue { i8*, i8* } %11, i8* %10, 1
  ret { i8*, i8* } %12
}

; core::fmt::Arguments::new_v1_formatted
; Function Attrs: inlinehint uwtable
define internal void @_ZN4core3fmt9Arguments16new_v1_formatted17hd5e9ced080c81dfaE(%"core::fmt::Arguments"* noalias nocapture sret dereferenceable(48), [0 x { [0 x i8]*, i64 }]* noalias nonnull readonly align 8 %pieces.0, i64 %pieces.1, [0 x { i8*, i8* }]* noalias nonnull readonly align 8 %args.0, i64 %args.1, [0 x %"core::fmt::rt::v1::Argument"]* noalias nonnull readonly align 8 %fmt.0, i64 %fmt.1) unnamed_addr #1 {
start:
  %_5 = alloca { i64*, i64 }, align 8
  %1 = bitcast { i64*, i64 }* %_5 to { [0 x %"core::fmt::rt::v1::Argument"]*, i64 }*
  %2 = getelementptr inbounds { [0 x %"core::fmt::rt::v1::Argument"]*, i64 }, { [0 x %"core::fmt::rt::v1::Argument"]*, i64 }* %1, i32 0, i32 0
  store [0 x %"core::fmt::rt::v1::Argument"]* %fmt.0, [0 x %"core::fmt::rt::v1::Argument"]** %2, align 8
  %3 = getelementptr inbounds { [0 x %"core::fmt::rt::v1::Argument"]*, i64 }, { [0 x %"core::fmt::rt::v1::Argument"]*, i64 }* %1, i32 0, i32 1
  store i64 %fmt.1, i64* %3, align 8
  %4 = bitcast %"core::fmt::Arguments"* %0 to { [0 x { [0 x i8]*, i64 }]*, i64 }*
  %5 = getelementptr inbounds { [0 x { [0 x i8]*, i64 }]*, i64 }, { [0 x { [0 x i8]*, i64 }]*, i64 }* %4, i32 0, i32 0
  store [0 x { [0 x i8]*, i64 }]* %pieces.0, [0 x { [0 x i8]*, i64 }]** %5, align 8
  %6 = getelementptr inbounds { [0 x { [0 x i8]*, i64 }]*, i64 }, { [0 x { [0 x i8]*, i64 }]*, i64 }* %4, i32 0, i32 1
  store i64 %pieces.1, i64* %6, align 8
  %7 = getelementptr inbounds %"core::fmt::Arguments", %"core::fmt::Arguments"* %0, i32 0, i32 3
  %8 = getelementptr inbounds { i64*, i64 }, { i64*, i64 }* %_5, i32 0, i32 0
  %9 = load i64*, i64** %8, align 8
  %10 = getelementptr inbounds { i64*, i64 }, { i64*, i64 }* %_5, i32 0, i32 1
  %11 = load i64, i64* %10, align 8
  %12 = getelementptr inbounds { i64*, i64 }, { i64*, i64 }* %7, i32 0, i32 0
  store i64* %9, i64** %12, align 8
  %13 = getelementptr inbounds { i64*, i64 }, { i64*, i64 }* %7, i32 0, i32 1
  store i64 %11, i64* %13, align 8
  %14 = getelementptr inbounds %"core::fmt::Arguments", %"core::fmt::Arguments"* %0, i32 0, i32 5
  %15 = getelementptr inbounds { [0 x { i8*, i8* }]*, i64 }, { [0 x { i8*, i8* }]*, i64 }* %14, i32 0, i32 0
  store [0 x { i8*, i8* }]* %args.0, [0 x { i8*, i8* }]** %15, align 8
  %16 = getelementptr inbounds { [0 x { i8*, i8* }]*, i64 }, { [0 x { i8*, i8* }]*, i64 }* %14, i32 0, i32 1
  store i64 %args.1, i64* %16, align 8
  ret void
}

; core::mem::size_of
; Function Attrs: inlinehint uwtable
define internal i64 @_ZN4core3mem7size_of17h24506033ef7ef062E() unnamed_addr #1 {
start:
  %tmp_ret = alloca i64, align 8
  store i64 16, i64* %tmp_ret, align 8
  %0 = load i64, i64* %tmp_ret, align 8
  br label %bb1

bb1:                                              ; preds = %start
  ret i64 %0
}

; core::mem::size_of
; Function Attrs: inlinehint uwtable
define internal i64 @_ZN4core3mem7size_of17h901aeab6d69720f2E() unnamed_addr #1 {
start:
  %tmp_ret = alloca i64, align 8
  store i64 4, i64* %tmp_ret, align 8
  %0 = load i64, i64* %tmp_ret, align 8
  br label %bb1

bb1:                                              ; preds = %start
  ret i64 %0
}

; core::ops::function::FnOnce::call_once
; Function Attrs: uwtable
define internal i32 @_ZN4core3ops8function6FnOnce9call_once17h27d755cee67a2edbE(i8* nonnull) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality {
start:
  %personalityslot = alloca { i8*, i32 }, align 8
  %arg1 = alloca {}, align 1
  %arg0 = alloca i8*, align 8
  store i8* %0, i8** %arg0, align 8
; invoke std::rt::lang_start::{{closure}}
  %1 = invoke i32 @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h6e1c450892b1f754E"(i8** align 8 dereferenceable(8) %arg0)
          to label %bb1 unwind label %cleanup

bb1:                                              ; preds = %start
  br label %bb2

bb2:                                              ; preds = %bb1
  ret i32 %1

bb3:                                              ; preds = %cleanup
  br label %bb4

bb4:                                              ; preds = %bb3
  %2 = bitcast { i8*, i32 }* %personalityslot to i8**
  %3 = load i8*, i8** %2, align 8
  %4 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %personalityslot, i32 0, i32 1
  %5 = load i32, i32* %4, align 8
  %6 = insertvalue { i8*, i32 } undef, i8* %3, 0
  %7 = insertvalue { i8*, i32 } %6, i32 %5, 1
  resume { i8*, i32 } %7

cleanup:                                          ; preds = %start
  %8 = landingpad { i8*, i32 }
          cleanup
  %9 = extractvalue { i8*, i32 } %8, 0
  %10 = extractvalue { i8*, i32 } %8, 1
  %11 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %personalityslot, i32 0, i32 0
  store i8* %9, i8** %11, align 8
  %12 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %personalityslot, i32 0, i32 1
  store i32 %10, i32* %12, align 8
  br label %bb3
}

; core::ops::function::FnOnce::call_once::{{vtable.shim}}
; Function Attrs: uwtable
define internal i32 @"_ZN4core3ops8function6FnOnce9call_once32_$u7b$$u7b$vtable.shim$u7d$$u7d$17hbfe54a791614f945E"(i8** %arg0) unnamed_addr #0 {
start:
  %arg1 = alloca {}, align 1
  %0 = load i8*, i8** %arg0, align 8, !nonnull !1
; call core::ops::function::FnOnce::call_once
  %1 = call i32 @_ZN4core3ops8function6FnOnce9call_once17h27d755cee67a2edbE(i8* nonnull %0)
  br label %bb1

bb1:                                              ; preds = %start
  ret i32 %1
}

; core::ptr::real_drop_in_place
; Function Attrs: uwtable
define internal void @_ZN4core3ptr18real_drop_in_place17h96afe4d514bb3c38E(i8** align 8 dereferenceable(8) %arg0) unnamed_addr #0 {
start:
  ret void
}

; core::ptr::<impl *mut T>::wrapping_add
; Function Attrs: inlinehint uwtable
define internal i8* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$12wrapping_add17h3f944d3e55c804bdE"(i8* %self, i64 %count) unnamed_addr #1 {
start:
; call core::ptr::<impl *mut T>::wrapping_offset
  %0 = call i8* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$15wrapping_offset17h835906e17eda2d9eE"(i8* %self, i64 %count)
  br label %bb1

bb1:                                              ; preds = %start
  ret i8* %0
}

; core::ptr::<impl *mut T>::wrapping_offset
; Function Attrs: inlinehint uwtable
define internal i8* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$15wrapping_offset17h835906e17eda2d9eE"(i8* %self, i64 %count) unnamed_addr #1 {
start:
  %tmp_ret = alloca i8*, align 8
  %0 = getelementptr i8, i8* %self, i64 %count
  store i8* %0, i8** %tmp_ret, align 8
  %1 = load i8*, i8** %tmp_ret, align 8
  br label %bb1

bb1:                                              ; preds = %start
  ret i8* %1
}

; core::ptr::<impl *mut T>::add
; Function Attrs: inlinehint uwtable
define internal [4 x i32]* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$3add17h8c3ba94a5f9e63b3E"([4 x i32]* %self, i64 %count) unnamed_addr #1 {
start:
; call core::ptr::<impl *mut T>::offset
  %0 = call [4 x i32]* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$6offset17hdf0bba33c31d7941E"([4 x i32]* %self, i64 %count)
  br label %bb1

bb1:                                              ; preds = %start
  ret [4 x i32]* %0
}

; core::ptr::<impl *mut T>::add
; Function Attrs: inlinehint uwtable
define internal i32* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$3add17he8137b02ed5a1862E"(i32* %self, i64 %count) unnamed_addr #1 {
start:
; call core::ptr::<impl *mut T>::offset
  %0 = call i32* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$6offset17h1a0a27c95852d960E"(i32* %self, i64 %count)
  br label %bb1

bb1:                                              ; preds = %start
  ret i32* %0
}

; core::ptr::<impl *mut T>::offset
; Function Attrs: inlinehint uwtable
define internal i32* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$6offset17h1a0a27c95852d960E"(i32* %self, i64 %count) unnamed_addr #1 {
start:
  %tmp_ret = alloca i32*, align 8
  %0 = getelementptr inbounds i32, i32* %self, i64 %count
  store i32* %0, i32** %tmp_ret, align 8
  %1 = load i32*, i32** %tmp_ret, align 8
  br label %bb1

bb1:                                              ; preds = %start
  ret i32* %1
}

; core::ptr::<impl *mut T>::offset
; Function Attrs: inlinehint uwtable
define internal [4 x i32]* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$6offset17hdf0bba33c31d7941E"([4 x i32]* %self, i64 %count) unnamed_addr #1 {
start:
  %tmp_ret = alloca [4 x i32]*, align 8
  %0 = getelementptr inbounds [4 x i32], [4 x i32]* %self, i64 %count
  store [4 x i32]* %0, [4 x i32]** %tmp_ret, align 8
  %1 = load [4 x i32]*, [4 x i32]** %tmp_ret, align 8
  br label %bb1

bb1:                                              ; preds = %start
  ret [4 x i32]* %1
}

; core::ptr::<impl *mut T>::is_null
; Function Attrs: inlinehint uwtable
define internal zeroext i1 @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17heb54d174dd3ad0e3E"([4 x i32]* %self) unnamed_addr #1 {
start:
  %0 = bitcast [4 x i32]* %self to i8*
; call core::ptr::null_mut
  %1 = call i8* @_ZN4core3ptr8null_mut17h236caeaa39cf68eeE()
  br label %bb1

bb1:                                              ; preds = %start
  %2 = icmp eq i8* %0, %1
  ret i1 %2
}

; core::ptr::<impl *mut T>::is_null
; Function Attrs: inlinehint uwtable
define internal zeroext i1 @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17hefda0dbc6462cbcdE"(i32* %self) unnamed_addr #1 {
start:
  %0 = bitcast i32* %self to i8*
; call core::ptr::null_mut
  %1 = call i8* @_ZN4core3ptr8null_mut17h236caeaa39cf68eeE()
  br label %bb1

bb1:                                              ; preds = %start
  %2 = icmp eq i8* %0, %1
  ret i1 %2
}

; core::ptr::null_mut
; Function Attrs: inlinehint uwtable
define internal i8* @_ZN4core3ptr8null_mut17h236caeaa39cf68eeE() unnamed_addr #1 {
start:
  ret i8* null
}

; core::slice::<impl [T]>::as_mut_ptr
; Function Attrs: inlinehint uwtable
define internal [4 x i32]* @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$10as_mut_ptr17h0cc7f77ba7a559f2E"([0 x [4 x i32]]* nonnull align 4 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %0 = bitcast [0 x [4 x i32]]* %self.0 to [4 x i32]*
  ret [4 x i32]* %0
}

; core::slice::<impl [T]>::as_mut_ptr
; Function Attrs: inlinehint uwtable
define internal i32* @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$10as_mut_ptr17hf0bc8639b7d66054E"([0 x i32]* nonnull align 4 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %0 = bitcast [0 x i32]* %self.0 to i32*
  ret i32* %0
}

; core::slice::<impl [T]>::len
; Function Attrs: inlinehint uwtable
define internal i64 @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$3len17hd158f8061ea13277E"([0 x [4 x i32]]* noalias nonnull readonly align 4 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %_2 = alloca %"core::slice::Repr<[i32; 4]>", align 8
  %0 = bitcast %"core::slice::Repr<[i32; 4]>"* %_2 to { [0 x [4 x i32]]*, i64 }*
  %1 = getelementptr inbounds { [0 x [4 x i32]]*, i64 }, { [0 x [4 x i32]]*, i64 }* %0, i32 0, i32 0
  store [0 x [4 x i32]]* %self.0, [0 x [4 x i32]]** %1, align 8
  %2 = getelementptr inbounds { [0 x [4 x i32]]*, i64 }, { [0 x [4 x i32]]*, i64 }* %0, i32 0, i32 1
  store i64 %self.1, i64* %2, align 8
  %3 = bitcast %"core::slice::Repr<[i32; 4]>"* %_2 to { i32*, i64 }*
  %4 = getelementptr inbounds { i32*, i64 }, { i32*, i64 }* %3, i32 0, i32 1
  %5 = load i64, i64* %4, align 8
  ret i64 %5
}

; core::slice::<impl [T]>::len
; Function Attrs: inlinehint uwtable
define internal i64 @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$3len17hfcd8fb803edc91ecE"([0 x i32]* noalias nonnull readonly align 4 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %_2 = alloca %"core::slice::Repr<i32>", align 8
  %0 = bitcast %"core::slice::Repr<i32>"* %_2 to { [0 x i32]*, i64 }*
  %1 = getelementptr inbounds { [0 x i32]*, i64 }, { [0 x i32]*, i64 }* %0, i32 0, i32 0
  store [0 x i32]* %self.0, [0 x i32]** %1, align 8
  %2 = getelementptr inbounds { [0 x i32]*, i64 }, { [0 x i32]*, i64 }* %0, i32 0, i32 1
  store i64 %self.1, i64* %2, align 8
  %3 = bitcast %"core::slice::Repr<i32>"* %_2 to { i32*, i64 }*
  %4 = getelementptr inbounds { i32*, i64 }, { i32*, i64 }* %3, i32 0, i32 1
  %5 = load i64, i64* %4, align 8
  ret i64 %5
}

; core::slice::<impl [T]>::iter_mut
; Function Attrs: inlinehint uwtable
define internal { i32*, i32* } @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$8iter_mut17h705dbea5bcc6571dE"([0 x i32]* nonnull align 4 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %_21 = alloca %"core::marker::PhantomData<&mut i32>", align 1
  %end = alloca i32*, align 8
  %_0 = alloca { i32*, i32* }, align 8
; call core::slice::<impl [T]>::as_mut_ptr
  %0 = call i32* @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$10as_mut_ptr17hf0bc8639b7d66054E"([0 x i32]* nonnull align 4 %self.0, i64 %self.1)
  br label %bb1

bb1:                                              ; preds = %start
; call core::ptr::<impl *mut T>::is_null
  %1 = call zeroext i1 @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17hefda0dbc6462cbcdE"(i32* %0)
  br label %bb2

bb2:                                              ; preds = %bb1
  %2 = xor i1 %1, true
  call void @llvm.assume(i1 %2)
  br label %bb3

bb3:                                              ; preds = %bb2
; call core::mem::size_of
  %3 = call i64 @_ZN4core3mem7size_of17h901aeab6d69720f2E()
  br label %bb4

bb4:                                              ; preds = %bb3
  %4 = icmp eq i64 %3, 0
  br i1 %4, label %bb5, label %bb6

bb5:                                              ; preds = %bb4
  %5 = bitcast i32* %0 to i8*
; call core::slice::<impl [T]>::len
  %6 = call i64 @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$3len17hfcd8fb803edc91ecE"([0 x i32]* noalias nonnull readonly align 4 %self.0, i64 %self.1)
  br label %bb7

bb6:                                              ; preds = %bb4
; call core::slice::<impl [T]>::len
  %7 = call i64 @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$3len17hfcd8fb803edc91ecE"([0 x i32]* noalias nonnull readonly align 4 %self.0, i64 %self.1)
  br label %bb9

bb7:                                              ; preds = %bb5
; call core::ptr::<impl *mut T>::wrapping_add
  %8 = call i8* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$12wrapping_add17h3f944d3e55c804bdE"(i8* %5, i64 %6)
  br label %bb8

bb8:                                              ; preds = %bb7
  %9 = bitcast i8* %8 to i32*
  store i32* %9, i32** %end, align 8
  br label %bb11

bb9:                                              ; preds = %bb6
; call core::ptr::<impl *mut T>::add
  %10 = call i32* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$3add17he8137b02ed5a1862E"(i32* %0, i64 %7)
  store i32* %10, i32** %end, align 8
  br label %bb10

bb10:                                             ; preds = %bb9
  br label %bb11

bb11:                                             ; preds = %bb10, %bb8
  %11 = load i32*, i32** %end, align 8
  %12 = bitcast { i32*, i32* }* %_0 to i32**
  store i32* %0, i32** %12, align 8
  %13 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %_0, i32 0, i32 1
  store i32* %11, i32** %13, align 8
  %14 = bitcast { i32*, i32* }* %_0 to %"core::marker::PhantomData<&mut i32>"*
  %15 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %_0, i32 0, i32 0
  %16 = load i32*, i32** %15, align 8
  %17 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %_0, i32 0, i32 1
  %18 = load i32*, i32** %17, align 8
  %19 = insertvalue { i32*, i32* } undef, i32* %16, 0
  %20 = insertvalue { i32*, i32* } %19, i32* %18, 1
  ret { i32*, i32* } %20
}

; core::slice::<impl [T]>::iter_mut
; Function Attrs: inlinehint uwtable
define internal { i32*, i32* } @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$8iter_mut17h9ec72aa0f1adbb13E"([0 x [4 x i32]]* nonnull align 4 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %_21 = alloca %"core::marker::PhantomData<&mut [i32; 4]>", align 1
  %end = alloca [4 x i32]*, align 8
  %_0 = alloca { i32*, i32* }, align 8
; call core::slice::<impl [T]>::as_mut_ptr
  %0 = call [4 x i32]* @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$10as_mut_ptr17h0cc7f77ba7a559f2E"([0 x [4 x i32]]* nonnull align 4 %self.0, i64 %self.1)
  br label %bb1

bb1:                                              ; preds = %start
; call core::ptr::<impl *mut T>::is_null
  %1 = call zeroext i1 @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17heb54d174dd3ad0e3E"([4 x i32]* %0)
  br label %bb2

bb2:                                              ; preds = %bb1
  %2 = xor i1 %1, true
  call void @llvm.assume(i1 %2)
  br label %bb3

bb3:                                              ; preds = %bb2
; call core::mem::size_of
  %3 = call i64 @_ZN4core3mem7size_of17h24506033ef7ef062E()
  br label %bb4

bb4:                                              ; preds = %bb3
  %4 = icmp eq i64 %3, 0
  br i1 %4, label %bb5, label %bb6

bb5:                                              ; preds = %bb4
  %5 = bitcast [4 x i32]* %0 to i8*
; call core::slice::<impl [T]>::len
  %6 = call i64 @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$3len17hd158f8061ea13277E"([0 x [4 x i32]]* noalias nonnull readonly align 4 %self.0, i64 %self.1)
  br label %bb7

bb6:                                              ; preds = %bb4
; call core::slice::<impl [T]>::len
  %7 = call i64 @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$3len17hd158f8061ea13277E"([0 x [4 x i32]]* noalias nonnull readonly align 4 %self.0, i64 %self.1)
  br label %bb9

bb7:                                              ; preds = %bb5
; call core::ptr::<impl *mut T>::wrapping_add
  %8 = call i8* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$12wrapping_add17h3f944d3e55c804bdE"(i8* %5, i64 %6)
  br label %bb8

bb8:                                              ; preds = %bb7
  %9 = bitcast i8* %8 to [4 x i32]*
  store [4 x i32]* %9, [4 x i32]** %end, align 8
  br label %bb11

bb9:                                              ; preds = %bb6
; call core::ptr::<impl *mut T>::add
  %10 = call [4 x i32]* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$3add17h8c3ba94a5f9e63b3E"([4 x i32]* %0, i64 %7)
  store [4 x i32]* %10, [4 x i32]** %end, align 8
  br label %bb10

bb10:                                             ; preds = %bb9
  br label %bb11

bb11:                                             ; preds = %bb10, %bb8
  %11 = load [4 x i32]*, [4 x i32]** %end, align 8
  %12 = bitcast { i32*, i32* }* %_0 to [4 x i32]**
  store [4 x i32]* %0, [4 x i32]** %12, align 8
  %13 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %_0, i32 0, i32 1
  %14 = bitcast i32** %13 to [4 x i32]**
  store [4 x i32]* %11, [4 x i32]** %14, align 8
  %15 = bitcast { i32*, i32* }* %_0 to %"core::marker::PhantomData<&mut [i32; 4]>"*
  %16 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %_0, i32 0, i32 0
  %17 = load i32*, i32** %16, align 8
  %18 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %_0, i32 0, i32 1
  %19 = load i32*, i32** %18, align 8
  %20 = insertvalue { i32*, i32* } undef, i32* %17, 0
  %21 = insertvalue { i32*, i32* } %20, i32* %19, 1
  ret { i32*, i32* } %21
}

; <() as std::process::Termination>::report
; Function Attrs: inlinehint uwtable
define internal i32 @"_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17ha97fdaad4e15facaE"() unnamed_addr #1 {
start:
; call <std::process::ExitCode as std::process::Termination>::report
  %0 = call i32 @"_ZN68_$LT$std..process..ExitCode$u20$as$u20$std..process..Termination$GT$6report17h269423f2b50d143fE"(i8 0)
  br label %bb1

bb1:                                              ; preds = %start
  ret i32 %0
}

; <I as core::iter::traits::IntoIterator>::into_iter
; Function Attrs: uwtable
define internal { i32*, i32* } @"_ZN54_$LT$I$u20$as$u20$core..iter..traits..IntoIterator$GT$9into_iter17h664642be175905efE"(i32* %self.0, i32* %self.1) unnamed_addr #0 {
start:
  %0 = insertvalue { i32*, i32* } undef, i32* %self.0, 0
  %1 = insertvalue { i32*, i32* } %0, i32* %self.1, 1
  ret { i32*, i32* } %1
}

; <I as core::iter::traits::IntoIterator>::into_iter
; Function Attrs: uwtable
define internal { i32*, i32* } @"_ZN54_$LT$I$u20$as$u20$core..iter..traits..IntoIterator$GT$9into_iter17h8263e821b42cf117E"(i32* %self.0, i32* %self.1) unnamed_addr #0 {
start:
  %0 = insertvalue { i32*, i32* } undef, i32* %self.0, 0
  %1 = insertvalue { i32*, i32* } %0, i32* %self.1, 1
  ret { i32*, i32* } %1
}

; <std::process::ExitCode as std::process::Termination>::report
; Function Attrs: inlinehint uwtable
define internal i32 @"_ZN68_$LT$std..process..ExitCode$u20$as$u20$std..process..Termination$GT$6report17h269423f2b50d143fE"(i8) unnamed_addr #1 {
start:
  %self = alloca i8, align 1
  store i8 %0, i8* %self, align 1
; call std::sys::unix::process::process_common::ExitCode::as_i32
  %1 = call i32 @_ZN3std3sys4unix7process14process_common8ExitCode6as_i3217h131bd83b3a6fff4bE(i8* noalias readonly align 1 dereferenceable(1) %self)
  br label %bb1

bb1:                                              ; preds = %start
  ret i32 %1
}

; <core::slice::IterMut<'a, T> as core::iter::iterator::Iterator>::next
; Function Attrs: inlinehint uwtable
define internal align 4 dereferenceable_or_null(16) i32* @"_ZN94_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$u20$as$u20$core..iter..iterator..Iterator$GT$4next17h54ce825ac39c65a6E"({ i32*, i32* }* align 8 dereferenceable(16) %self) unnamed_addr #1 {
start:
  %_0.i = alloca [4 x i32]*, align 8
  %_0 = alloca i32*, align 8
  %0 = bitcast { i32*, i32* }* %self to [4 x i32]**
  %1 = load [4 x i32]*, [4 x i32]** %0, align 8
; call core::ptr::<impl *mut T>::is_null
  %2 = call zeroext i1 @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17heb54d174dd3ad0e3E"([4 x i32]* %1)
  br label %bb1

bb1:                                              ; preds = %start
  %3 = xor i1 %2, true
  call void @llvm.assume(i1 %3)
  br label %bb2

bb2:                                              ; preds = %bb1
; call core::mem::size_of
  %4 = call i64 @_ZN4core3mem7size_of17h24506033ef7ef062E()
  br label %bb3

bb3:                                              ; preds = %bb2
  %5 = icmp ne i64 %4, 0
  br i1 %5, label %bb4, label %bb7

bb4:                                              ; preds = %bb3
  %6 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %self, i32 0, i32 1
  %7 = bitcast i32** %6 to [4 x i32]**
  %8 = load [4 x i32]*, [4 x i32]** %7, align 8
; call core::ptr::<impl *mut T>::is_null
  %9 = call zeroext i1 @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17heb54d174dd3ad0e3E"([4 x i32]* %8)
  br label %bb5

bb5:                                              ; preds = %bb4
  %10 = xor i1 %9, true
  call void @llvm.assume(i1 %10)
  br label %bb6

bb6:                                              ; preds = %bb5
  br label %bb7

bb7:                                              ; preds = %bb6, %bb3
  %11 = bitcast { i32*, i32* }* %self to [4 x i32]**
  %12 = load [4 x i32]*, [4 x i32]** %11, align 8
  %13 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %self, i32 0, i32 1
  %14 = bitcast i32** %13 to [4 x i32]**
  %15 = load [4 x i32]*, [4 x i32]** %14, align 8
  %16 = icmp eq [4 x i32]* %12, %15
  br i1 %16, label %bb8, label %bb9

bb8:                                              ; preds = %bb7
  %17 = bitcast i32** %_0 to {}**
  store {}* null, {}** %17, align 8
  br label %bb11

bb9:                                              ; preds = %bb7
; call core::mem::size_of
  %18 = call i64 @_ZN4core3mem7size_of17h24506033ef7ef062E()
  %19 = icmp eq i64 %18, 0
  br i1 %19, label %bb2.i, label %bb3.i

bb2.i:                                            ; preds = %bb9
  %20 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %self, i32 0, i32 1
  %21 = bitcast i32** %20 to [4 x i32]**
  %22 = load [4 x i32]*, [4 x i32]** %21, align 8
  %23 = bitcast [4 x i32]* %22 to i8*
; call core::ptr::<impl *mut T>::wrapping_offset
  %24 = call i8* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$15wrapping_offset17h835906e17eda2d9eE"(i8* %23, i64 -1)
  %25 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %self, i32 0, i32 1
  %26 = bitcast i32** %25 to [4 x i32]**
  %27 = bitcast i8* %24 to [4 x i32]*
  store [4 x i32]* %27, [4 x i32]** %26, align 8
  %28 = bitcast { i32*, i32* }* %self to [4 x i32]**
  %29 = load [4 x i32]*, [4 x i32]** %28, align 8
  store [4 x i32]* %29, [4 x i32]** %_0.i, align 8
  br label %"_ZN52_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$GT$14post_inc_start17hcb37536d44dd9294E.exit"

bb3.i:                                            ; preds = %bb9
  %30 = bitcast { i32*, i32* }* %self to [4 x i32]**
  %31 = load [4 x i32]*, [4 x i32]** %30, align 8
  %32 = bitcast { i32*, i32* }* %self to [4 x i32]**
  %33 = load [4 x i32]*, [4 x i32]** %32, align 8
; call core::ptr::<impl *mut T>::offset
  %34 = call [4 x i32]* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$6offset17hdf0bba33c31d7941E"([4 x i32]* %33, i64 1)
  %35 = bitcast { i32*, i32* }* %self to [4 x i32]**
  store [4 x i32]* %34, [4 x i32]** %35, align 8
  store [4 x i32]* %31, [4 x i32]** %_0.i, align 8
  br label %"_ZN52_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$GT$14post_inc_start17hcb37536d44dd9294E.exit"

"_ZN52_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$GT$14post_inc_start17hcb37536d44dd9294E.exit": ; preds = %bb2.i, %bb3.i
  %36 = load [4 x i32]*, [4 x i32]** %_0.i, align 8
  br label %bb10

bb10:                                             ; preds = %"_ZN52_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$GT$14post_inc_start17hcb37536d44dd9294E.exit"
  %37 = bitcast i32** %_0 to [4 x i32]**
  store [4 x i32]* %36, [4 x i32]** %37, align 8
  br label %bb11

bb11:                                             ; preds = %bb10, %bb8
  %38 = load i32*, i32** %_0, align 8
  ret i32* %38
}

; <core::slice::IterMut<'a, T> as core::iter::iterator::Iterator>::next
; Function Attrs: inlinehint uwtable
define internal align 4 dereferenceable_or_null(4) i32* @"_ZN94_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$u20$as$u20$core..iter..iterator..Iterator$GT$4next17hb33d39b685e46f5aE"({ i32*, i32* }* align 8 dereferenceable(16) %self) unnamed_addr #1 {
start:
  %_0.i = alloca i32*, align 8
  %_0 = alloca i32*, align 8
  %0 = bitcast { i32*, i32* }* %self to i32**
  %1 = load i32*, i32** %0, align 8
; call core::ptr::<impl *mut T>::is_null
  %2 = call zeroext i1 @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17hefda0dbc6462cbcdE"(i32* %1)
  br label %bb1

bb1:                                              ; preds = %start
  %3 = xor i1 %2, true
  call void @llvm.assume(i1 %3)
  br label %bb2

bb2:                                              ; preds = %bb1
; call core::mem::size_of
  %4 = call i64 @_ZN4core3mem7size_of17h901aeab6d69720f2E()
  br label %bb3

bb3:                                              ; preds = %bb2
  %5 = icmp ne i64 %4, 0
  br i1 %5, label %bb4, label %bb7

bb4:                                              ; preds = %bb3
  %6 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %self, i32 0, i32 1
  %7 = load i32*, i32** %6, align 8
; call core::ptr::<impl *mut T>::is_null
  %8 = call zeroext i1 @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17hefda0dbc6462cbcdE"(i32* %7)
  br label %bb5

bb5:                                              ; preds = %bb4
  %9 = xor i1 %8, true
  call void @llvm.assume(i1 %9)
  br label %bb6

bb6:                                              ; preds = %bb5
  br label %bb7

bb7:                                              ; preds = %bb6, %bb3
  %10 = bitcast { i32*, i32* }* %self to i32**
  %11 = load i32*, i32** %10, align 8
  %12 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %self, i32 0, i32 1
  %13 = load i32*, i32** %12, align 8
  %14 = icmp eq i32* %11, %13
  br i1 %14, label %bb8, label %bb9

bb8:                                              ; preds = %bb7
  %15 = bitcast i32** %_0 to {}**
  store {}* null, {}** %15, align 8
  br label %bb11

bb9:                                              ; preds = %bb7
; call core::mem::size_of
  %16 = call i64 @_ZN4core3mem7size_of17h901aeab6d69720f2E()
  %17 = icmp eq i64 %16, 0
  br i1 %17, label %bb2.i, label %bb3.i

bb2.i:                                            ; preds = %bb9
  %18 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %self, i32 0, i32 1
  %19 = load i32*, i32** %18, align 8
  %20 = bitcast i32* %19 to i8*
; call core::ptr::<impl *mut T>::wrapping_offset
  %21 = call i8* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$15wrapping_offset17h835906e17eda2d9eE"(i8* %20, i64 -1)
  %22 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %self, i32 0, i32 1
  %23 = bitcast i8* %21 to i32*
  store i32* %23, i32** %22, align 8
  %24 = bitcast { i32*, i32* }* %self to i32**
  %25 = load i32*, i32** %24, align 8
  store i32* %25, i32** %_0.i, align 8
  br label %"_ZN52_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$GT$14post_inc_start17hc5ed644c66d4790dE.exit"

bb3.i:                                            ; preds = %bb9
  %26 = bitcast { i32*, i32* }* %self to i32**
  %27 = load i32*, i32** %26, align 8
  %28 = bitcast { i32*, i32* }* %self to i32**
  %29 = load i32*, i32** %28, align 8
; call core::ptr::<impl *mut T>::offset
  %30 = call i32* @"_ZN4core3ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$6offset17h1a0a27c95852d960E"(i32* %29, i64 1)
  %31 = bitcast { i32*, i32* }* %self to i32**
  store i32* %30, i32** %31, align 8
  store i32* %27, i32** %_0.i, align 8
  br label %"_ZN52_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$GT$14post_inc_start17hc5ed644c66d4790dE.exit"

"_ZN52_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$GT$14post_inc_start17hc5ed644c66d4790dE.exit": ; preds = %bb2.i, %bb3.i
  %32 = load i32*, i32** %_0.i, align 8
  br label %bb10

bb10:                                             ; preds = %"_ZN52_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$GT$14post_inc_start17hc5ed644c66d4790dE.exit"
  store i32* %32, i32** %_0, align 8
  br label %bb11

bb11:                                             ; preds = %bb10, %bb8
  %33 = load i32*, i32** %_0, align 8
  ret i32* %33
}

; Function Attrs: noinline uwtable
define void @f(%BI* align 4 dereferenceable(32) %w) unnamed_addr #2 {
start:
  %_24 = alloca i32*, align 8
  %iter2 = alloca { i32*, i32* }, align 8
  %_result1 = alloca {}, align 1
  %_9 = alloca i32*, align 8
  %iter = alloca { i32*, i32* }, align 8
  %_result = alloca {}, align 1
  %0 = bitcast %BI* %w to [2 x [4 x i32]]*
  %1 = bitcast [2 x [4 x i32]]* %0 to [0 x [4 x i32]]*
; call core::slice::<impl [T]>::iter_mut
  %2 = call { i32*, i32* } @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$8iter_mut17h9ec72aa0f1adbb13E"([0 x [4 x i32]]* nonnull align 4 %1, i64 2)
  %3 = extractvalue { i32*, i32* } %2, 0
  %4 = extractvalue { i32*, i32* } %2, 1
  br label %bb1

bb1:                                              ; preds = %start
; call <I as core::iter::traits::IntoIterator>::into_iter
  %5 = call { i32*, i32* } @"_ZN54_$LT$I$u20$as$u20$core..iter..traits..IntoIterator$GT$9into_iter17h664642be175905efE"(i32* %3, i32* %4)
  %6 = extractvalue { i32*, i32* } %5, 0
  %7 = extractvalue { i32*, i32* } %5, 1
  br label %bb2

bb2:                                              ; preds = %bb1
  %8 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %iter, i32 0, i32 0
  store i32* %6, i32** %8, align 8
  %9 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %iter, i32 0, i32 1
  store i32* %7, i32** %9, align 8
  br label %bb3

bb3:                                              ; preds = %bb12, %bb2
; call <core::slice::IterMut<'a, T> as core::iter::iterator::Iterator>::next
  %10 = call align 4 dereferenceable_or_null(16) i32* @"_ZN94_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$u20$as$u20$core..iter..iterator..Iterator$GT$4next17h54ce825ac39c65a6E"({ i32*, i32* }* align 8 dereferenceable(16) %iter)
  store i32* %10, i32** %_9, align 8
  br label %bb4

bb4:                                              ; preds = %bb3
  %11 = bitcast i32** %_9 to {}**
  %12 = load {}*, {}** %11, align 8
  %13 = icmp eq {}* %12, null
  %14 = select i1 %13, i64 0, i64 1
  switch i64 %14, label %bb6 [
    i64 0, label %bb5
    i64 1, label %bb7
  ]

bb5:                                              ; preds = %bb4
  ret void

bb6:                                              ; preds = %bb11, %bb4
  unreachable

bb7:                                              ; preds = %bb4
  %15 = bitcast i32** %_9 to [4 x i32]**
  %16 = load [4 x i32]*, [4 x i32]** %15, align 8, !nonnull !1
  %17 = bitcast [4 x i32]* %16 to [0 x i32]*
; call core::slice::<impl [T]>::iter_mut
  %18 = call { i32*, i32* } @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$8iter_mut17h705dbea5bcc6571dE"([0 x i32]* nonnull align 4 %17, i64 4)
  %19 = extractvalue { i32*, i32* } %18, 0
  %20 = extractvalue { i32*, i32* } %18, 1
  br label %bb8

bb8:                                              ; preds = %bb7
; call <I as core::iter::traits::IntoIterator>::into_iter
  %21 = call { i32*, i32* } @"_ZN54_$LT$I$u20$as$u20$core..iter..traits..IntoIterator$GT$9into_iter17h8263e821b42cf117E"(i32* %19, i32* %20)
  %22 = extractvalue { i32*, i32* } %21, 0
  %23 = extractvalue { i32*, i32* } %21, 1
  br label %bb9

bb9:                                              ; preds = %bb8
  %24 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %iter2, i32 0, i32 0
  store i32* %22, i32** %24, align 8
  %25 = getelementptr inbounds { i32*, i32* }, { i32*, i32* }* %iter2, i32 0, i32 1
  store i32* %23, i32** %25, align 8
  br label %bb10

bb10:                                             ; preds = %bb13, %bb9
; call <core::slice::IterMut<'a, T> as core::iter::iterator::Iterator>::next
  %26 = call align 4 dereferenceable_or_null(4) i32* @"_ZN94_$LT$core..slice..IterMut$LT$$u27$a$C$$u20$T$GT$$u20$as$u20$core..iter..iterator..Iterator$GT$4next17hb33d39b685e46f5aE"({ i32*, i32* }* align 8 dereferenceable(16) %iter2)
  store i32* %26, i32** %_24, align 8
  br label %bb11

bb11:                                             ; preds = %bb10
  %27 = bitcast i32** %_24 to {}**
  %28 = load {}*, {}** %27, align 8
  %29 = icmp eq {}* %28, null
  %30 = select i1 %29, i64 0, i64 1
  switch i64 %30, label %bb6 [
    i64 0, label %bb12
    i64 1, label %bb13
  ]

bb12:                                             ; preds = %bb11
  br label %bb3

bb13:                                             ; preds = %bb11
  %31 = load i32*, i32** %_24, align 8, !nonnull !1
  store i32 0, i32* %31, align 4
  br label %bb10
}

; test::main
; Function Attrs: uwtable
define internal void @_ZN4test4main17h21e0b94bad749a9eE() unnamed_addr #0 {
start:
  %_17 = alloca i32*, align 8
  %_16 = alloca [1 x { i8*, i8* }], align 8
  %_9 = alloca %"core::fmt::Arguments", align 8
  %_4 = alloca [4 x i32], align 4
  %_3 = alloca [2 x [4 x i32]], align 4
  %_2 = alloca %BI, align 4
  %0 = getelementptr inbounds [4 x i32], [4 x i32]* %_4, i64 0, i64 0
  %1 = bitcast i32* %0 to i8*
  call void @llvm.memset.p0i8.i64(i8* align 4 %1, i8 0, i64 16, i1 false)
  %2 = getelementptr inbounds [2 x [4 x i32]], [2 x [4 x i32]]* %_3, i64 0, i64 0
  %3 = getelementptr inbounds [2 x [4 x i32]], [2 x [4 x i32]]* %_3, i64 0, i64 2
  br label %repeat_loop_header

bb1:                                              ; preds = %repeat_loop_next
  br label %bb2

bb2:                                              ; preds = %bb1
  br label %bb3

bb3:                                              ; preds = %bb2
  %4 = bitcast %BI* %_2 to [2 x [4 x i32]]*
  %5 = getelementptr inbounds [2 x [4 x i32]], [2 x [4 x i32]]* %4, i64 0, i64 1
  %6 = getelementptr inbounds [4 x i32], [4 x i32]* %5, i64 0, i64 3
  store i32* %6, i32** %_17, align 8
  %7 = load i32*, i32** %_17, align 8, !nonnull !1
; call core::fmt::ArgumentV1::new
  %8 = call { i8*, i8* } @_ZN4core3fmt10ArgumentV13new17h0af350dc6d28844eE(i32* noalias readonly align 4 dereferenceable(4) %7, i1 (i32*, %"core::fmt::Formatter"*)* nonnull @"_ZN4core3fmt3num52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i32$GT$3fmt17h7a9374c1576dce31E")
  %9 = extractvalue { i8*, i8* } %8, 0
  %10 = extractvalue { i8*, i8* } %8, 1
  br label %bb4

bb4:                                              ; preds = %bb3
  %11 = bitcast [1 x { i8*, i8* }]* %_16 to { i8*, i8* }*
  %12 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %11, i32 0, i32 0
  store i8* %9, i8** %12, align 8
  %13 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %11, i32 0, i32 1
  store i8* %10, i8** %13, align 8
  %14 = bitcast [1 x { i8*, i8* }]* %_16 to [0 x { i8*, i8* }]*
; call core::fmt::Arguments::new_v1_formatted
  call void @_ZN4core3fmt9Arguments16new_v1_formatted17hd5e9ced080c81dfaE(%"core::fmt::Arguments"* noalias nocapture sret dereferenceable(48) %_9, [0 x { [0 x i8]*, i64 }]* noalias nonnull readonly align 8 bitcast (<{ i8*, [8 x i8], i8*, [8 x i8] }>* @2 to [0 x { [0 x i8]*, i64 }]*), i64 2, [0 x { i8*, i8* }]* noalias nonnull readonly align 8 %14, i64 1, [0 x %"core::fmt::rt::v1::Argument"]* noalias nonnull readonly align 8 bitcast (<{ [64 x i8] }>* @3 to [0 x %"core::fmt::rt::v1::Argument"]*), i64 1)
  br label %bb5

bb5:                                              ; preds = %bb4
; call std::io::stdio::_print
  call void @_ZN3std2io5stdio6_print17hdec9324a4622df1eE(%"core::fmt::Arguments"* noalias nocapture dereferenceable(48) %_9)
  br label %bb6

bb6:                                              ; preds = %bb5
  ret void

repeat_loop_header:                               ; preds = %repeat_loop_body, %start
  %15 = phi [4 x i32]* [ %2, %start ], [ %19, %repeat_loop_body ]
  %16 = icmp ne [4 x i32]* %15, %3
  br i1 %16, label %repeat_loop_body, label %repeat_loop_next

repeat_loop_body:                                 ; preds = %repeat_loop_header
  %17 = bitcast [4 x i32]* %15 to i8*
  %18 = bitcast [4 x i32]* %_4 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %17, i8* align 4 %18, i64 16, i1 false)
  %19 = getelementptr inbounds [4 x i32], [4 x i32]* %15, i64 1
  br label %repeat_loop_header

repeat_loop_next:                                 ; preds = %repeat_loop_header
  %20 = bitcast %BI* %_2 to [2 x [4 x i32]]*
  %21 = bitcast [2 x [4 x i32]]* %20 to i8*
  %22 = bitcast [2 x [4 x i32]]* %_3 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %21, i8* align 4 %22, i64 32, i1 false)
  call void @f(%BI* align 4 dereferenceable(32) %_2)
  br label %bb1
}

; std::rt::lang_start_internal
; Function Attrs: uwtable
declare i64 @_ZN3std2rt19lang_start_internal17h3dc68cf5532522d7E({}* nonnull align 1, [3 x i64]* noalias readonly align 8 dereferenceable(24), i64, i8**) unnamed_addr #0

; Function Attrs: nounwind uwtable
declare i32 @rust_eh_personality(i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*) unnamed_addr #3

; Function Attrs: nounwind
declare void @llvm.assume(i1) #4

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i1) #5

; core::fmt::num::<impl core::fmt::Display for i32>::fmt
; Function Attrs: uwtable
declare zeroext i1 @"_ZN4core3fmt3num52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i32$GT$3fmt17h7a9374c1576dce31E"(i32* noalias readonly align 4 dereferenceable(4), %"core::fmt::Formatter"* align 8 dereferenceable(96)) unnamed_addr #0

; std::io::stdio::_print
; Function Attrs: uwtable
declare void @_ZN3std2io5stdio6_print17hdec9324a4622df1eE(%"core::fmt::Arguments"* noalias nocapture dereferenceable(48)) unnamed_addr #0

define i32 @main(i32, i8**) unnamed_addr #6 {
top:
  %2 = sext i32 %0 to i64
; call std::rt::lang_start
  %3 = call i64 @_ZN3std2rt10lang_start17h4f32aa1279b9079fE(void ()* @_ZN4test4main17h21e0b94bad749a9eE, i64 %2, i8** %1)
  %4 = trunc i64 %3 to i32
  ret i32 %4
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1) #5

attributes #0 = { uwtable "no-frame-pointer-elim"="true" "probe-stack"="__rust_probestack" "target-cpu"="core2" }
attributes #1 = { inlinehint uwtable "no-frame-pointer-elim"="true" "probe-stack"="__rust_probestack" "target-cpu"="core2" }
attributes #2 = { noinline uwtable "no-frame-pointer-elim"="true" "probe-stack"="__rust_probestack" "target-cpu"="core2" }
attributes #3 = { nounwind uwtable "no-frame-pointer-elim"="true" "probe-stack"="__rust_probestack" "target-cpu"="core2" }
attributes #4 = { nounwind }
attributes #5 = { argmemonly nounwind }
attributes #6 = { "no-frame-pointer-elim"="true" "target-cpu"="core2" }

!llvm.module.flags = !{!0}

!0 = !{i32 7, !"PIE Level", i32 2}
!1 = !{}
