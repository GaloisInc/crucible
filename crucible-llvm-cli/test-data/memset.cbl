(declare @memset ((dst (Ptr 64)) (val (Bitvector 32)) (count (Bitvector 64))) (Ptr 64))

(defun @main () Unit
  (start start:
    (let p (alloca none (bv 64 8)))
    (let c (bv 32 0))
    (let sz (bv 64 4))
    (let _ (funcall @memset p c sz))
    (return ())))
