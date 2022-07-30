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
; test-multinv.c:7:3
(declare-fun y () (_ BitVec 8))
; success
(define-fun x!0 () (_ BitVec 64) (concat (ite (= ((_ extract 7 7) y) (_ bv1 1)) (_ bv72057594037927935 56) (_ bv0 56)) y))
; success
(declare-fun x () (_ BitVec 8))
; success
(define-fun x!1 () (_ BitVec 64) (concat (ite (= ((_ extract 7 7) x) (_ bv1 1)) (_ bv72057594037927935 56) (_ bv0 56)) x))
; success
(define-fun x!2 () (_ BitVec 64) (bvmul x!0 x!1))
; success
(define-fun x!3 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) x) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) x))
; success
(define-fun x!4 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) y) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) y))
; success
(define-fun x!5 () (_ BitVec 32) (bvmul x!3 x!4))
; success
(define-fun x!6 () (_ BitVec 64) (concat (ite (= ((_ extract 31 31) x!5) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) x!5))
; success
(define-fun x!7 () Bool (= x!2 x!6))
; success
(define-fun x!8 () Bool (not x!7))
; success
(assert (! x!8 :named x!9))
; success
(check-sat)
; unsat
(get-unsat-core)
; (
; x!9
; )
(pop 1)
; success
(define-fun x!10 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) x) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) x))
; success
(define-fun x!11 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) y) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) y))
; success
(define-fun x!12 () (_ BitVec 32) (bvmul x!10 x!11))
; success
(define-fun x!13 () Bool (= (_ bv0 32) x!12))
; success
(define-fun x!14 () Bool (not x!13))
; success
(assert (! x!14 :named x!15))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b11001101))
(get-value (y))
; ((y #b10100111))
(pop 1)
; success
(exit)
; success
