(declare @llvm.scmp.i2.i32 ((x (Bitvector 32)) (y (Bitvector 32))) (Bitvector 2))

(defun @main () Unit
  (start start:
    (let x (bv 32 -1))
    (let y (bv 32 1))
    (let r0 (funcall @llvm.scmp.i2.i32 x y))
    (let r1 (funcall @llvm.scmp.i2.i32 x x))
    (let r2 (funcall @llvm.scmp.i2.i32 y x))
    (assert! (equal? r0 (bv 2 -1)) "r0 == -1")
    (assert! (equal? r1 (bv 2 0)) "r1 == 0")
    (assert! (equal? r2 (bv 2 1)) "r2 == 1")
    (return ())))
