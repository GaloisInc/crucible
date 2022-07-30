(set-option :print-success true)
; success
(set-option :produce-models true)
; success
(set-option :global-declarations true)
; success
(set-option :produce-unsat-cores true)
; success
(set-logic ALL_SUPPORTED)
; success
(get-info :error-behavior)
; (:error-behavior immediate-exit)
(push 1)
; success
; test-trans.c:8:3
(declare-fun y () (_ BitVec 8))
; success
(declare-fun x () (_ BitVec 8))
; success
(define-fun x!0 () Bool (bvslt y x))
; success
(assert (! x!0 :named x!1))
; success
; test-trans.c:9:3
(declare-fun z () (_ BitVec 8))
; success
(define-fun x!2 () Bool (bvslt z x))
; success
(define-fun x!3 () Bool (not x!2))
; success
(assert (! x!3 :named x!4))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b10000001))
(get-value (y))
; ((y #b10000000))
(get-value (z))
; ((z #b00101010))
(pop 1)
; success
(exit)
; success
