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
; ./cFiles32bit/test-trans-32.c:8:3
(declare-fun y () (_ BitVec 32))
; success
(declare-fun x () (_ BitVec 32))
; success
(define-fun x!0 () Bool (bvslt y x))
; success
(assert (! x!0 :named x!1))
; success
; ./cFiles32bit/test-trans-32.c:9:3
(declare-fun z () (_ BitVec 32))
; success
(define-fun x!2 () Bool (bvslt z x))
; success
(define-fun x!3 () Bool (not x!2))
; success
(assert (! x!3 :named x!4))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b11111111111111111111111111111111))
(get-value (y))
; ((y #b10000000000000000000000000000001))
(get-value (z))
; ((z #b00000000000000000000000000000001))
(get-abduct abd x!2 )
