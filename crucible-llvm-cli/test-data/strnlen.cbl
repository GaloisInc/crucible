(declare @strnlen ((s (Ptr 64)) (l (Bitvector 64))) (Bitvector 64))

(defun @main () Unit
  (start start:
    (let z (ptr 8 0 (bv 8 0)))

    (let p0 (alloca none (bv 64 1)))
    (store none i8 p0 z)
    (let l0 (funcall @strnlen p0 (bv 64 0)))
    (assert! (equal? l0 (bv 64 0)) "strnlen('', 0) = 0")
    (let l0b (funcall @strnlen p0 (bv 64 10)))
    (assert! (equal? l0b (bv 64 0)) "strnlen('', 10) = 0")

    (let q0 (alloca none (bv 64 2)))
    (let a (ptr 8 0 (bv 8 97))) ; 'a'
    (store none i8 q0 a)
    (let q1 (ptr-add-offset q0 (bv 64 1)))
    (store none i8 q1 z)
    (let l1 (funcall @strnlen q0 (bv 64 1)))
    (assert! (equal? l1 (bv 64 1)) "strnlen('a', 1) = 1")
    (let l1b (funcall @strnlen q0 (bv 64 2)))
    (assert! (equal? l1b (bv 64 1)) "strnlen('a', 2) = 1")
    (let l1c (funcall @strnlen q0 (bv 64 0)))
    (assert! (equal? l1c (bv 64 0)) "strnlen('a', 0) = 0")

    (let r0 (alloca none (bv 64 2)))
    (let f (fresh (Bitvector 8)))
    (let c (ptr 8 0 f))
    (store none i8 r0 c)
    (let r1 (ptr-add-offset r0 (bv 64 1)))
    (store none i8 r1 z)
    (let l2 (funcall @strnlen r0 (bv 64 1)))
    (assert! (<= l2 (bv 64 1)) "strnlen(..., 1) of (<=1)-length string is <=1")
    (let l2b (funcall @strnlen r0 (bv 64 2)))
    (assert! (<= l2b (bv 64 1)) "strnlen(..., 2) of (<=1)-length string is <=1")

    (let s0 (alloca none (bv 64 3)))
    (let x1 (ptr 8 0 (bv 8 65))) ; 'A'
    (let x2 (ptr 8 0 (bv 8 66))) ; 'B'
    (store none i8 s0 x1)
    (let s1 (ptr-add-offset s0 (bv 64 1)))
    (store none i8 s1 x2)
    (let s2 (ptr-add-offset s0 (bv 64 2)))
    (let g (fresh (Bitvector 8)))
    (assume! (not (equal? g (bv 8 0))) "g != 0")
    (let gptr (ptr 8 0 g))
    (store none i8 s2 gptr)
    (let l3 (funcall @strnlen s0 (bv 64 2)))
    (assert! (equal? l3 (bv 64 2)) "strnlen(..., 2) when first 2 bytes non-null is 2")
    (let l4 (funcall @strnlen s0 (bv 64 3)))
    (assert! (equal? l4 (bv 64 3)) "strnlen(..., 3) when first 3 bytes non-null is 3")

    (return ())))
