(set-option :produce-models true)
(set-option :global-declarations true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-logic ALL)

; test-trans.c:8:3
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))

(assert (bvsgt x y))
(get-abduct abd (bvsgt x z))
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)