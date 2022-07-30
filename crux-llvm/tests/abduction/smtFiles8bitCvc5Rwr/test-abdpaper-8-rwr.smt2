(set-option :produce-models true)
(set-option :global-declarations true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-logic ALL)

; test-abdpaper.c:7:3
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))

(assert (bvsgt y #x00))

(get-abduct abd (bvsgt (bvadd x y z) #x00))
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)
