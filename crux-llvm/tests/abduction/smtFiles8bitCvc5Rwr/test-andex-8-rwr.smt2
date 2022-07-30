(set-option :produce-models true)
(set-option :global-declarations true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-logic ALL)

; test-andex.c:7:3
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(get-abduct abd (= (bvand x y) #x01))
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)