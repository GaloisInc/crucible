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
; ./cFiles8bit/test-addident-8.c:7:3
(declare-fun y () (_ BitVec 8))
; success
(define-fun x!0 () Bool (= (_ bv0 8) y))
; success
(define-fun x!1 () Bool (not x!0))
; success
(assert (! x!1 :named x!2))
; success
(check-sat)
; sat
(get-value (y))
; ((y #b11111111))
(get-abduct abd x!0 )
