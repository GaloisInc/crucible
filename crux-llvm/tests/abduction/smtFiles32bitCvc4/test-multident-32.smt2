(set-option :print-success true)
; success
(set-option :produce-models true)
; success
(set-option :global-declarations true)
; success
(set-option :produce-unsat-cores true)
; success
(set-logic ALL_SUPPORTED)
; success
(get-info :error-behavior)
; (:error-behavior immediate-exit)
(push 1)
; success
(push 1)
; success
; test-multident-32.c:7:3
(declare-fun y () (_ BitVec 32))
; success
(define-fun x!0 () (_ BitVec 64) (concat (ite (= ((_ extract 31 31) y) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) y))
; success
(declare-fun x () (_ BitVec 32))
; success
(define-fun x!1 () (_ BitVec 64) (concat (ite (= ((_ extract 31 31) x) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) x))
; success
(define-fun x!2 () (_ BitVec 64) (bvmul x!0 x!1))
; success
(define-fun x!3 () (_ BitVec 32) (bvmul x y))
; success
(define-fun x!4 () (_ BitVec 64) (concat (ite (= ((_ extract 31 31) x!3) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) x!3))
; success
(define-fun x!5 () Bool (= x!2 x!4))
; success
(define-fun x!6 () Bool (not x!5))
; success
(assert (! x!6 :named x!7))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b10000000000000000000000000011001))
(get-value (y))
; ((y #b10000000000000000000000000000000))
(pop 1)
; success
(define-fun x!8 () (_ BitVec 32) (bvmul x y))
; success
(define-fun x!9 () Bool (= x!8 x))
; success
(define-fun x!10 () Bool (not x!9))
; success
(assert (! x!10 :named x!11))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b10000000000001010000010000011001))
(get-value (y))
; ((y #b10000000000000000000000000000000))
(pop 1)
; success
(exit)
; success
