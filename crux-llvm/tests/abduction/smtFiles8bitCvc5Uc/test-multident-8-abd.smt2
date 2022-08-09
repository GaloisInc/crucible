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
; ./cFiles8bit/test-multident-8.c:7:19
(declare-fun x () (_ BitVec 8))
; success
(declare-fun y () (_ BitVec 8))
; success
(define-fun x!0 () (_ BitVec 8) (bvmul x y))
; success
(define-fun x!1 () Bool (= x!0 x))
; success
(define-fun x!2 () Bool (not x!1))
; success
(push 2)
; success
(assert (! x!2 :named x!3))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b11111111))
(get-value (y))
; ((y #b00000000))
(pop 2)
; success
(get-abduct abd x!1 )
; (define-fun abd () Bool (bvult x #b00000001))
(get-abduct-next)
; (define-fun abd () Bool (= #b00000001 y))
(get-abduct-next)
; (define-fun abd () Bool (= (bvsdiv x y) x))
(pop 1)
; success
(exit)
; success
