(set-option :produce-models true)
(set-option :global-declarations true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-logic ALL)

; test-file.c:10:3
(declare-fun x () (_ BitVec 8))

(assert (bvslt x #x64))
(get-abduct abd (bvslt (bvadd x #x01) #x64))
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)