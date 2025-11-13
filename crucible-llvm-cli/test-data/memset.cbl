(declare @memset ((dst (Ptr 64)) (val (Bitvector 32)) (count (Ptr 64))) (Ptr 64))

(defun @main () Unit
  (start start:
    (let p (alloca none (bv 64 8)))
    (let c (bv 32 0))
    (let sz (ptr 64 0 (bv 64 4)))
    (let _ (funcall @memset p c sz))
    (return ())))
