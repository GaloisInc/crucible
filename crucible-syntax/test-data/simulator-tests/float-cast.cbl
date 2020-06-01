
(defun @main () Unit
  (start start:
    (let a (fresh (FP Double)))
    (let b (fp-to-binary a))   
    (let c (binary-to-fp Double b))

    (println (show b))
    (println (show c))

    (let x (fresh (Bitvector 64)))
    (let y (binary-to-fp Double x))
    (let z (fp-to-binary y))

    (println (show y))
    (println (show z))

    (let u (fp-to-ubv 64 rne a))
    (println (show u))
    (assert! (equal? a (ubv-to-fp Double rne u)) "bad unsigned round trip")

    (let s (fp-to-sbv 64 rne a))
    (println (show s))
    (assert! (equal? a (sbv-to-fp Double rne s)) "bad signed round trip")

    (return ()))
)
