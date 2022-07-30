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
(assert (! x!9 :named x!10))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b01111111111111111111111111111111))
(get-value (y))
; ((y #b00000000000000000000000000000001))
(get-abduct abd x!8 )
