(set-option :print-success true)
; success
(set-option :produce-models true)
; success
(set-option :global-declarations true)
; success
(set-option :produce-abducts true)
; success
(set-logic ALL)
; success
(get-info :error-behavior)
; (:error-behavior immediate-exit)
(push 1)
; success
; ./cFiles8bit/test-maxint-8.c:7:3
(declare-fun x () (_ BitVec 8))
; success
(define-fun x!0 () Bool (= (_ bv255 8) x))
; success
(push 2)
; success
(assert (! x!0 :named x!1))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b11111111))
(pop 2)
; success
(define-fun x!2 () Bool (not x!0))
; success
(get-abduct abd x!2 )
; (define-fun abd () Bool (= #b00000000 x))
(get-abduct-next)
; (define-fun abd () Bool (= x #b00000001))
(get-abduct-next)
; (define-fun abd () Bool (bvult x #b11111111))
(pop 1)
; success
(exit)
; success
