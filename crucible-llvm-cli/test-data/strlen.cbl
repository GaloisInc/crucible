(declare @strlen ((s (Ptr 64))) (Bitvector 64))

(defun @main () Unit
  (start start:

    (let p0 (alloca none (bv 64 1)))
    (let z (ptr 8 0 (bv 8 0)))
    (store none i8 p0 z)
    (let l0 (funcall @strlen p0))
    (assert! (equal? l0 (bv 64 0)) "strlen() of 0-length string is 0")

    (let q0 (alloca none (bv 64 2)))
    (let a (ptr 8 0 (bv 8 97))) ; 'a'
    (store none i8 q0 a)
    (let q1 (ptr-add-offset q0 (bv 64 1)))
    (store none i8 q1 z)
    (let l1 (funcall @strlen q0))
    (assert! (equal? l1 (bv 64 1)) "strlen() of 1-length string is 1")

    (let r0 (alloca none (bv 64 2)))
    (let f (fresh (Bitvector 8)))
    (let c (ptr 8 0 f))
    (store none i8 r0 c)
    (let r1 (ptr-add-offset r0 (bv 64 1)))
    (store none i8 r1 z)
    (let l2 (funcall @strlen r0))
    (assert! (<= l2 (bv 64 1)) "strlen() of (<=1)-length string is <=1")

    (return ())))
