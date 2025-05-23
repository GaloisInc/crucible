(declare @read-bytes ((x Pointer)) (Vector (Bitvector 8)))
(declare @read-c-string ((x Pointer)) (String Unicode))
(declare @write-bytes ((dest Pointer) (src (Vector (Bitvector 8)))) Unit)
(declare @write-c-string ((dst Pointer) (src (String Unicode))) Unit)

(defun @main () Unit
  (start start:

    (let p (alloca none (bv 64 6)))
    (funcall @write-c-string p "hello")
    (let s (funcall @read-c-string p))
    (assert! (equal? s "hello") "strings should be equal")

    (let q (alloca none (bv 64 4)))
	(let v (vector (bv 8 4) (bv 8 9) (bv 8 0)))
    (funcall @write-bytes q v)
    (let b (funcall @read-bytes p))

    (return ())))
