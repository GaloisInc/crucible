(declare @llvm.expect.i1 ((x (Bitvector 1)) (y (Bitvector 1))) (Bitvector 1))

(defun @main () Unit
  (start start:
    (let x (bv 1 0))
    (let y (bv 1 1))
    (let v (funcall @llvm.expect.i1 x y))
	(assert! (equal? v x) "v == x")
    (return ())))
