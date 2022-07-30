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
; test-file.c:10:3
(declare-fun x () (_ BitVec 8))
; success
(define-fun x!0 () Bool (bvslt x (_ bv100 8)))
; success
(assert (! x!0 :named x!1))
; success
; test-file.c:5:12
(define-fun x!2 () (_ BitVec 8) (bvadd x (_ bv1 8)))
; success
(define-fun x!3 () Bool (bvslt x!2 (_ bv100 8)))
; success
(define-fun x!4 () Bool (not x!3))
; success
(assert (! x!4 :named x!5))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b01100011))
(pop 1)
; success
(exit)
; success
