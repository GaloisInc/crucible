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
; test-maxint-32.c:6:3
(declare-fun x () (_ BitVec 32))
; success
(define-fun x!0 () Bool (= (_ bv4294967295 32) x))
; success
(assert (! x!0 :named x!1))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b11111111111111111111111111111111))
(pop 1)
; success
(exit)
; success
