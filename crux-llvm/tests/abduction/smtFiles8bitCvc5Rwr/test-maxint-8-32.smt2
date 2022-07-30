(set-option :produce-models true)
(set-option :global-declarations true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-logic ALL)

; test-maxint32.c:6:3
(declare-fun x () (_ BitVec 8))

(get-abduct abd (bvsgt (bvadd x #x01) x))
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)
(get-abduct-next)