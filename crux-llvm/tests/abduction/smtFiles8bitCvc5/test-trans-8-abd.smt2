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
; ./cFiles8bit/test-trans-8.c:8:3
(declare-fun y () (_ BitVec 8))
; success
(declare-fun x () (_ BitVec 8))
; success
(define-fun x!0 () Bool (bvslt y x))
; success
(assert (! x!0 :named x!1))
; success
; ./cFiles8bit/test-trans-8.c:9:3
(declare-fun z () (_ BitVec 8))
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
; ((x #b11111111))
(get-value (y))
; ((y #b10000001))
(get-value (z))
; ((z #b00000001))
(get-abduct abd x!2 )
