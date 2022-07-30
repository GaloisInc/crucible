(set-option :produce-models true)
(set-option :global-declarations true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-logic ALL)

; test-addinv.c:8:3
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(get-abduct abd (= (bvadd x y) #x00))
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)