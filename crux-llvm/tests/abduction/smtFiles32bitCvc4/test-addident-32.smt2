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
; test-addident-32.c:7:3
(declare-fun y () (_ BitVec 32))
; success
(define-fun x!0 () Bool (= (_ bv0 32) y))
; success
(define-fun x!1 () Bool (not x!0))
; success
(assert (! x!1 :named x!2))
; success
(check-sat)
; sat
(get-value (y))
; ((y #b00000000000000000000000000000001))
(pop 1)
; success
(exit)
; success
