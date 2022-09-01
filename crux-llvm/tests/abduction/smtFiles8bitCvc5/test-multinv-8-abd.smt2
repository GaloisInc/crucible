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
; ./cFiles8bit/test-multinv-8.c:7:19
(declare-fun x () (_ BitVec 8))
; success
(declare-fun y () (_ BitVec 8))
; success
(define-fun x!0 () (_ BitVec 8) (bvmul x y))
; success
(define-fun x!1 () Bool (= (_ bv0 8) x!0))
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
; ((x #b00000001))
(get-value (y))
; ((y #b00000001))
(pop 2)
; success
(get-abduct abd x!1)
; (define-fun abd () Bool (= x #b00000000))
(get-abduct-next)
; (define-fun abd () Bool (= y #b00000000))
(get-abduct-next)
; (define-fun abd () Bool (= (bvmul y x) #b00000000))
(pop 1)
; success
(exit)
; success
