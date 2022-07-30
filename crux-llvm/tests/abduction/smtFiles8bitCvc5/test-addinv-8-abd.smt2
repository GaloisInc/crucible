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
(push 1)
; success
; ./cFiles8bit/test-addinv-8.c:7:3
(declare-fun y () (_ BitVec 8))
; success
(define-fun x!0 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) y) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) y))
; success
(define-fun x!1 () Bool (bvslt x!0 (_ bv0 32)))
; success
(define-fun x!2 () (_ BitVec 32) (bvneg x!0))
; success
(define-fun x!3 () Bool (bvslt x!2 (_ bv0 32)))
; success
(define-fun x!4 () Bool (and x!1 x!3))
; success
(define-fun x!5 () Bool (not x!4))
; success
(define-fun x!6 () Bool (not x!5))
; success
(assert (! x!6 :named x!7))
; success
(check-sat)
; unsat
(pop 1)
; success
(declare-fun x () (_ BitVec 8))
; success
(define-fun x!8 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) x) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) x))
; success
(define-fun x!9 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) y) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) y))
; success
(define-fun x!10 () (_ BitVec 32) (bvneg x!9))
; success
(define-fun x!11 () Bool (= x!8 x!10))
; success
(define-fun x!12 () Bool (not x!11))
; success
(assert (! x!12 :named x!13))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b10000000))
(get-value (y))
; ((y #b10000000))
(get-abduct abd x!11 )