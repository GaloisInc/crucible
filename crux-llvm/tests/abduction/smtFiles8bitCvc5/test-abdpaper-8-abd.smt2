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
; ./cFiles8bit/test-abdpaper-8.c:8:3
(declare-fun y () (_ BitVec 8))
; success
(define-fun x!0 () Bool (bvslt (_ bv0 8) y))
; success
(assert (! x!0 :named x!1))
; success
(push 1)
; success
(define-fun x!2 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) y) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) y))
; success
(define-fun x!3 () Bool (bvslt x!2 (_ bv0 32)))
; success
; ./cFiles8bit/test-abdpaper-8.c:9:3
(declare-fun x () (_ BitVec 8))
; success
(define-fun x!4 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) x) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) x))
; success
(define-fun x!5 () Bool (bvslt x!4 (_ bv0 32)))
; success
(define-fun x!6 () (_ BitVec 32) (bvadd x!4 x!2))
; success
(define-fun x!7 () Bool (bvslt x!6 (_ bv0 32)))
; success
(define-fun x!8 () Bool (and x!3 x!5 (not x!7)))
; success
(define-fun x!9 () Bool (and (not x!3) (not x!5) x!7))
; success
(define-fun x!10 () Bool (and (not x!8) (not x!9)))
; success
(define-fun x!11 () Bool (not x!10))
; success
(assert (! x!11 :named x!12))
; success
(check-sat)
; unsat
(pop 1)
; success
(push 1)
; success
; ./cFiles8bit/test-abdpaper-8.c:8:3
(define-fun x!13 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) y) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) y))
; success
; ./cFiles8bit/test-abdpaper-8.c:9:3
(define-fun x!14 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) x) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) x))
; success
(define-fun x!15 () (_ BitVec 32) (bvadd x!14 x!13))
; success
(define-fun x!16 () Bool (bvslt x!15 (_ bv0 32)))
; success
(declare-fun z () (_ BitVec 8))
; success
(define-fun x!17 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) z) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) z))
; success
(define-fun x!18 () Bool (bvslt x!17 (_ bv0 32)))
; success
(define-fun x!19 () (_ BitVec 32) (bvadd (bvadd x!17 x!14) x!13))
; success
(define-fun x!20 () Bool (bvslt x!19 (_ bv0 32)))
; success
(define-fun x!21 () Bool (and x!16 x!18 (not x!20)))
; success
(define-fun x!22 () Bool (and (not x!16) (not x!18) x!20))
; success
(define-fun x!23 () Bool (and (not x!21) (not x!22)))
; success
(define-fun x!24 () Bool (not x!23))
; success
(assert (! x!24 :named x!25))
; success
(check-sat)
; unsat
(pop 1)
; success
; ./cFiles8bit/test-abdpaper-8.c:8:3
(define-fun x!26 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) y) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) y))
; success
; ./cFiles8bit/test-abdpaper-8.c:9:3
(define-fun x!27 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) x) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) x))
; success
(define-fun x!28 () (_ BitVec 32) (concat (ite (= ((_ extract 7 7) z) (_ bv1 1)) (_ bv16777215 24) (_ bv0 24)) z))
; success
(define-fun x!29 () (_ BitVec 32) (bvadd (bvadd x!28 x!27) x!26))
; success
(define-fun x!30 () Bool (bvslt (_ bv0 32) x!29))
; success
(define-fun x!31 () Bool (not x!30))
; success
(assert (! x!31 :named x!32))
; success
(check-sat)
; sat
(get-value (x))
; ((x #b00000000))
(get-value (y))
; ((y #b00000001))
(get-value (z))
; ((z #b10000000))
(get-abduct abd x!30 )
