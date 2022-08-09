(set-option :print-success true)
; success
(set-option :produce-models true)
; success
(set-option :global-declarations true)
; success
(set-option :produce-unsat-cores true)
; success
(set-option :produce-abducts true)
; success
(set-logic ALL)
; success
(get-info :error-behavior)
; (:error-behavior immediate-exit)
(push 1)
; success
; ./cFiles32bit/test-file-32.c:10:3
(declare-fun x () (_ BitVec 32))
; success
(define-fun x!0 () Bool (bvslt x (_ bv100 32)))
; success
(assert (! x!0 :named x!1))
; success
(push 1)
; success
; ./cFiles32bit/test-file-32.c:5:12
(define-fun x!2 () Bool (bvslt x (_ bv0 32)))
; success
(define-fun x!3 () (_ BitVec 32) (bvadd x (_ bv1 32)))
; success
(define-fun x!4 () Bool (bvslt x!3 (_ bv0 32)))
; success
(define-fun x!5 () Bool (and (not x!2) x!4))
; success
(define-fun x!6 () Bool (not x!5))
; success
(define-fun x!7 () Bool (not x!6))
; success
(push 2)
; success
(assert (! x!7 :named x!8))
; success
(check-sat)
; unsat
(get-unsat-core)
; (
; x!1
; x!8
; )
(pop 2)
; success
(pop 1)
; success
(define-fun x!9 () (_ BitVec 32) (bvadd x (_ bv1 32)))
; success
(define-fun x!10 () Bool (bvslt x!9 (_ bv100 32)))
; success
(define-fun x!11 () Bool (not x!10))
; success
(push 2)
; success
(assert (! x!11 :named x!12))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b00000000000000000000000001100011))
(pop 2)
; success
(get-abduct abd x!10 )
; (define-fun abd () Bool (bvult x #b00000000000000000000000000000001))
(get-abduct-next)
; (define-fun abd () Bool (bvult #b00000000000000000000000001100100 x))
(get-abduct-next)
; (define-fun abd () Bool (= #b00000000000000000000000000000001 x))
(pop 1)
; success
(exit)
; success
