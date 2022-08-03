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
; ./cFiles32bit/test-maxint-32.c:6:3
(declare-fun x () (_ BitVec 32))
; success
(define-fun x!0 () Bool (= (_ bv4294967295 32) x))
; success
(push 2)
; success
(assert (! x!0 :named x!1))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b11111111111111111111111111111111))
(pop 2)
; success
(define-fun x!2 () Bool (not x!0))
; (error "Parse Error: <stdin>:15.32: Overloaded constants must be type cast.")
(pop 1)
