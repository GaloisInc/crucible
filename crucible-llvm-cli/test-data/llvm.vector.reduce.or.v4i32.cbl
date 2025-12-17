(declare @llvm.vector.reduce.or.v4i32 ((x (Vector (Bitvector 32)))) (Bitvector 32))

(defun @main () Unit
  (start start:
    (let x (vector (bv 32 1) (bv 32 2) (bv 32 4) (bv 32 8)))
    (let y (funcall @llvm.vector.reduce.or.v4i32 x))
    (assert! (equal? y (bv 32 15)) "y == 15")
    (return ())))
