(defun @bv-test () Unit
  (start start:
    (let f (fresh (Bitvector 12)))
    (let a (bv 1 99))
    (let x (bv 12 0))
    (let y (bv 12 -1))
    (let p (equal? x y))
    (let z (if p x (- (bv 12 123) y)))
    (let q (+ (bv-xor x y) x))
    (let qz (zero-extend 16 q))
    (let qs (sign-extend 16 (negate q)))
    (let qq (bv-concat qz qs))
    (let q2 (bv-trunc 11 qq))
    (let asdf (bv-select 5 3 x))

    (let p2 (and
       (< x y) (<= x y) (<$ x y) (<=$ x y) (bv-nonzero f)
       (bv-carry x y) (bv-scarry x y) (bv-sborrow x y)
       ))

    (let allarith
       (+ (- x y) (* x y q) (/ x y) (mod x y)
          (/$ x y) (smod x y)))

    (let allbitwise
       (bv-xor x (bv-or x y q) (bv-and x y) (bv-not x)
         (shl x y) (lshr x y) (ashr x y) (bool-to-bv 12 p)))

    (return ()))
)
