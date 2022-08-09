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
; ./cFiles32bit/test-addinv-32.c:7:3
(declare-fun y () (_ BitVec 32))
; success
(define-fun x!0 () (_ BitVec 32) (bvneg y))
; success
(declare-fun x () (_ BitVec 32))
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
; ((x #b11111111111111111111111111111110))
(get-value (y))
; ((y #b11111111111111111111111111111111))
(pop 2)
; success
(get-abduct abd x!1 )
; (define-fun abd () Bool (= (bvneg y) x))
(get-abduct-next)
