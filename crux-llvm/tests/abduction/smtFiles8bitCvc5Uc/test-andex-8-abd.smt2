(set-option :print-success true)
; success
(set-option :produce-models true)
; success
(set-option :global-declarations true)
; success
(set-option :produce-unsat-cores true)
; success
(set-option :produce-abducts true)
; success
(set-logic ALL)
; success
(get-info :error-behavior)
; (:error-behavior immediate-exit)
(push 1)
; success
; ./cFiles8bit/test-andex-8.c:7:3
(declare-fun x () (_ BitVec 8))
; success
(define-fun x!0 () Bool (= (_ bv1 8) x))
; success
(assert (! x!0 :named x!1))
; success
; ./cFiles8bit/test-andex-8.c:8:20
(declare-fun y () (_ BitVec 8))
; success
(define-fun x!2 () (_ BitVec 8) (bvand x y))
; success
(define-fun x!3 () Bool (= (_ bv1 8) x!2))
; success
(define-fun x!4 () Bool (not x!3))
; success
(push 2)
; success
(assert (! x!4 :named x!5))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b00000001))
(get-value (y))
; ((y #b00000000))
(pop 2)
; success
(get-abduct abd x!3 )
; (define-fun abd () Bool (= #b00000001 y))
(get-abduct-next)
; (define-fun abd () Bool (bvult #b00000000 (bvand y #b00000001)))
(get-abduct-next)
