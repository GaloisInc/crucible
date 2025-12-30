(declare @llvm.vector.reduce.umax.v4i32 ((x (Vector (Bitvector 32)))) (Bitvector 32))

(defun @main () Unit
  (start start:
    (let x (vector (bv 32 1) (bv 32 2) (bv 32 3) (bv 32 4)))
    (let y (funcall @llvm.vector.reduce.umax.v4i32 x))
    (assert! (equal? y (bv 32 4)) "y == 4")
    (return ())))
