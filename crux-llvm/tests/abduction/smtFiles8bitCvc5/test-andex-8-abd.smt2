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
; ./cFiles8bit/test-andex-8.c:7:3
(declare-fun y () (_ BitVec 8))
; success
(define-fun x!0 () Bool (= (_ bv1 8) y))
; success
(define-fun x!1 () (_ BitVec 1) (ite x!0 (_ bv1 1) (_ bv0 1)))
; success
(define-fun x!2 () (_ BitVec 8) (concat (_ bv0 7) x!1))
; success
(declare-fun x () (_ BitVec 8))
; success
(define-fun x!3 () (_ BitVec 8) (bvand x!2 x))
; success
(define-fun x!4 () Bool (= (_ bv0 8) x!3))
; success
(assert (! x!4 :named x!5))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b00000001))
(get-value (y))
; ((y #b11111111))
(define-fun x!6 () Bool (not x!4))
; (error "Parse Error: <stdin>:19.32: Overloaded constants must be type cast.")
(pop 1)
