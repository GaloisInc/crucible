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
; ./cFiles32bit/test-abdpaper-32.c:8:3
(declare-fun y () (_ BitVec 32))
; success
(define-fun x!0 () Bool (bvslt (_ bv0 32) y))
; success
(assert (! x!0 :named x!1))
; success
(push 1)
; success
; ./cFiles32bit/test-abdpaper-32.c:9:3
(define-fun x!2 () Bool (bvslt y (_ bv0 32)))
; success
(declare-fun x () (_ BitVec 32))
; success
(define-fun x!3 () Bool (bvslt x (_ bv0 32)))
; success
(define-fun x!4 () (_ BitVec 32) (bvadd y x))
; success
(define-fun x!5 () Bool (bvslt x!4 (_ bv0 32)))
; success
(define-fun x!6 () Bool (and x!2 x!3 (not x!5)))
; success
(define-fun x!7 () Bool (and (not x!2) (not x!3) x!5))
; success
(define-fun x!8 () Bool (and (not x!6) (not x!7)))
; success
(define-fun x!9 () Bool (not x!8))
; success
(push 2)
; success
(assert (! x!9 :named x!10))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b01000000000000000000000000000000))
(get-value (y))
; ((y #b01000000000000000000000000000000))
(pop 2)
; success
(get-abduct abd x!8 )
; (define-fun abd () Bool (bvult x #b00000000000000000000000000000001))
(get-abduct-next)
; (define-fun abd () Bool (bvult (bvshl x #b00000000000000000000000000000001) #b00000000000000000000000000000001))
(get-abduct-next)
; (define-fun abd () Bool (bvult (bvshl x #b00000000000000000000000000000001) x))
(pop 1)
; success
(push 1)
; success
(define-fun x!11 () (_ BitVec 32) (bvadd y x))
; success
(define-fun x!12 () Bool (bvslt x!11 (_ bv0 32)))
; success
(declare-fun z () (_ BitVec 32))
; success
(define-fun x!13 () Bool (bvslt z (_ bv0 32)))
; success
(define-fun x!14 () (_ BitVec 32) (bvadd (bvadd z y) x))
; success
(define-fun x!15 () Bool (bvslt x!14 (_ bv0 32)))
; success
(define-fun x!16 () Bool (and x!12 x!13 (not x!15)))
; success
(define-fun x!17 () Bool (and (not x!12) (not x!13) x!15))
; success
(define-fun x!18 () Bool (and (not x!16) (not x!17)))
; success
(define-fun x!19 () Bool (not x!18))
; success
(push 2)
; success
(assert (! x!19 :named x!20))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b00100000000110100000000000000000))
(get-value (y))
; ((y #b01111111110010100000000000000000))
(get-value (z))
; ((z #b10011111111001000000000000000000))
(get-value (x!11))
; ((x!11 #b10011111111001000000000000000000))
(pop 2)
; success
(get-abduct abd x!18 )
; (define-fun abd () Bool (= z #b00000000000000000000000000000000))
(get-abduct-next)
