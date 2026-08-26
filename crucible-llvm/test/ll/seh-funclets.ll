; Regression test for Windows SEH instruction translation.
;
; This .ll exercises every new pattern case added by
; GaloisInc/crucible#1839 by parsing the bitcode (via the bumped
; llvm-pretty-bc-parser submodule), then invoking translateModule
; from crucible-llvm.  The accompanying seh-funclets.checks file is
; empty -- the test runner in Tests.hs treats that as a
; "translation must succeed without exception" assertion (see the
; "" case in transCheck).
;
; What this regression-guards:
;
;   * Translation/Instruction.hs `generateInstr` cases for the five
;     SEH opcodes:  CleanupPad / CatchPad / CleanupRet / CatchRet /
;     CatchSwitch.  Without these, an incomplete-pattern match in
;     generateInstr would crash translation of any function
;     containing SEH.  They route to `unsupported`, so the resulting
;     Crucible CFG raises a runtime error if executed, but
;     translation itself must succeed.
;
;   * Translation/BlockInfo.hs `buildSuccSet` cases for the three
;     SEH terminators (CatchRet / CleanupRet / CatchSwitch).
;     Without these the predecessor map for any SEH-containing
;     function would be wrong, silently corrupting downstream
;     analyses.
;
;   * Translation/BlockInfo.hs `instrUse` cases for all five SEH
;     opcodes.  Without these, live-variable analysis on
;     SEH-containing functions would be incomplete.
;
;   * The 13-site operand-bundle pattern adapter on Call / Invoke /
;     CallBr (BlockInfo.hs, Instruction.hs, Globals.hs,
;     Translation.hs).  The bundle-bearing `call void @log_failure(...)
;     ["funclet"(token %p1)]` below forces the adapter to thread
;     the bundle field through every constructor application.
;
; We use the Itanium @__gxx_personality_v0 personality (rather than
; the MSVC @__CxxFrameHandler3) so that this .ll passes `llvm-as`
; even when CI is using a non-Windows LLVM build.  The IR verifier
; still accepts a "funclet" operand bundle under the Itanium
; personality; it just does not *require* one.
;
; Target triple intentionally omitted -- we just need this to
; assemble + parse + translate; we do not need a specific target.

declare void @may_throw()
declare void @log_failure(i32)
declare i32 @__gxx_personality_v0(...)

; Exercises:
;   * invoke (with empty bundle list -- the adapter must still apply)
;   * catchswitch within none [...] unwind to caller
;   * catchpad within %cs [ptr null]
;   * catchret to label
define void @test_catch() personality ptr @__gxx_personality_v0 {
entry:
  invoke void @may_throw()
          to label %cont unwind label %cs

cont:
  ret void

cs:
  %cs0 = catchswitch within none [label %catch] unwind to caller

catch:
  %p0 = catchpad within %cs0 [ptr null]
  catchret from %p0 to label %cont
}

; Exercises:
;   * invoke
;   * cleanuppad within none []
;   * cleanupret with explicit unwind label
;   * a second cleanuppad reached via that unwind label, terminating
;     with cleanupret "unwind to caller"
;   * call carrying a "funclet" operand bundle (forces the operand
;     bundle adapter to round-trip through translation)
define void @test_cleanup() personality ptr @__gxx_personality_v0 {
entry:
  invoke void @may_throw()
          to label %cont unwind label %cleanup1

cont:
  ret void

cleanup1:
  %p1 = cleanuppad within none []
  call void @log_failure(i32 1) [ "funclet"(token %p1) ]
  cleanupret from %p1 unwind label %cleanup2

cleanup2:
  %p2 = cleanuppad within none []
  cleanupret from %p2 unwind to caller
}

; Exercises:
;   * catchswitch with multiple handlers AND an explicit default
;     unwind destination (forces both branches of the SEH terminator
;     successor-set logic in BlockInfo.buildSuccSet)
;   * catchpad with multiple arguments
;   * a nested cleanuppad whose parent is the catchpad token
define void @test_nested() personality ptr @__gxx_personality_v0 {
entry:
  invoke void @may_throw()
          to label %cont unwind label %cs

cont:
  ret void

cs:
  %cs0 = catchswitch within none [label %catch1, label %catch2] unwind label %cleanup

catch1:
  %p1 = catchpad within %cs0 [ptr null, i32 64, ptr null]
  catchret from %p1 to label %cont

catch2:
  %p2 = catchpad within %cs0 [ptr null]
  ; Cleanup nested inside a catch funclet -- parent token is the catchpad,
  ; not "none".  The IR verifier requires that a cleanupret inside a catch
  ; unwind to the same destination as the parent catchswitch (here %cleanup).
  invoke void @may_throw() [ "funclet"(token %p2) ]
          to label %cont unwind label %nested_cleanup

nested_cleanup:
  %p3 = cleanuppad within %p2 []
  cleanupret from %p3 unwind label %cleanup

cleanup:
  %p4 = cleanuppad within none []
  cleanupret from %p4 unwind to caller
}
