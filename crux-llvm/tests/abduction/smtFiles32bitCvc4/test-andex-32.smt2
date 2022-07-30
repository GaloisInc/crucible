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
; test-andex-32.c:7:3
(declare-fun y () (_ BitVec 32))
; success
(define-fun x!0 () Bool (= (_ bv1 32) y))
; success
(define-fun x!1 () (_ BitVec 1) (ite x!0 (_ bv1 1) (_ bv0 1)))
; success
(define-fun x!2 () (_ BitVec 32) (concat (_ bv0 31) x!1))
; success
(declare-fun x () (_ BitVec 32))
; success
(define-fun x!3 () (_ BitVec 32) (bvand x!2 x))
; success
(define-fun x!4 () (_ BitVec 8) ((_ extract 7 0) x!3))
; success
(define-fun x!5 () Bool (= (_ bv0 8) x!4))
; success
(assert (! x!5 :named x!6))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b00000000000000000000000000000000))
(get-value (y))
; ((y #b00000000000000000000000000000001))
(pop 1)
; success
(exit)
; success
