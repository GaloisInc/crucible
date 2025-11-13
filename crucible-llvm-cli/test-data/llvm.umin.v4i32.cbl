(declare @llvm.umin.v4i32 ((x (Vector (Bitvector 32))) (y (Vector (Bitvector 32)))) (Vector (Bitvector 32)))

(defun @main () Unit
  (start start:
    (let x (vector (bv 32 1) (bv 32 2) (bv 32 3) (bv 32 4)))
    (let y (vector (bv 32 4) (bv 32 3) (bv 32 2) (bv 32 1)))
    (let v (funcall @llvm.umin.v4i32 x y))
    (let v0 (vector-get v 0))
    (let v1 (vector-get v 1))
    (let v2 (vector-get v 2))
    (let v3 (vector-get v 3))
    (assert! (equal? v0 (bv 32 1)) "v0 == 1")
    (assert! (equal? v1 (bv 32 2)) "v1 == 2")
    (assert! (equal? v2 (bv 32 2)) "v2 == 2")
    (assert! (equal? v3 (bv 32 1)) "v3 == 1")
    (return ())))
