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
; ./cFiles8bit/test-abdpaper-8.c:8:3
(declare-fun y () (_ BitVec 8))
; success
(define-fun x!0 () Bool (bvslt (_ bv0 8) y))
; success
(assert (! x!0 :named x!1))
; success
; ./cFiles8bit/test-abdpaper-8.c:9:22
(declare-fun x () (_ BitVec 8))
; success
(declare-fun z () (_ BitVec 8))
; success
(define-fun x!2 () (_ BitVec 8) (bvadd (bvadd z y) x))
; success
(define-fun x!3 () Bool (bvslt (_ bv0 8) x!2))
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
; ((x #b01111111))
(get-value (y))
; ((y #b00000011))
(get-value (z))
; ((z #b11111111))
(pop 2)
; success
(get-abduct abd x!3 )
; (define-fun abd () Bool (= (bvshl z x) x))
(get-abduct-next)
; (define-fun abd () Bool (= (bvadd x z) #b00000000))
(get-abduct-next)
