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
; ./cFiles32bit/test-addident-32-2.c:5:19
(declare-fun y () (_ BitVec 32))
; success
(define-fun x!0 () Bool (bvslt y (_ bv0 32)))           ;y < 0
; success
(declare-fun x () (_ BitVec 32))
; success
(define-fun x!1 () Bool (bvslt x (_ bv0 32)))           ;x < 0
; success
(define-fun x!2 () (_ BitVec 32) (bvadd y x))           ;y + x
; success
(define-fun x!3 () Bool (bvslt x!2 (_ bv0 32)))         ;y + x < 0
; success
(define-fun x!4 () Bool (and x!0 x!1 (not x!3)))        ;(y < 0) ^ (x < 0) ^ ~(y + x < 0)
; success
(define-fun x!5 () Bool (and (not x!0) (not x!1) x!3))  ;~(y < 0) ^ ~(x < 0) ^ (y + x < 0)
; success
(define-fun x!6 () Bool (and (not x!4) (not x!5)))      
;~[(y < 0) ^ (x < 0) ^ ~(y + x < 0)] ^ ~[~(y < 0) ^ ~(x < 0) ^ (y + x < 0)]
;[~(y < 0) ^ ~(x < 0) ^ (y + x < 0)] ^ [(y < 0) ^ (x < 0) ^ ~(y + x < 0)]
; success
(define-fun x!7 () Bool (not x!6))
;~([~(y < 0) ^ ~(x < 0) ^ (y + x < 0)] ^ [(y < 0) ^ (x < 0) ^ ~(y + x < 0)])
;~[~(y < 0) ^ ~(x < 0) ^ (y + x < 0)] v ~[(y < 0) ^ (x < 0) ^ ~(y + x < 0)]
;[(y < 0) v (x < 0) v ~(y + x < 0)] v [~(y < 0) v ~(x < 0) v (y + x < 0)]
; success
(assert (! x!7 :named x!8))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b01111111111111111111111111111111))
(get-value (y))
; ((y #b00000000000000000000000000000001))
(get-abduct abd x!6 )
