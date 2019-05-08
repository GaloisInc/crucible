;; This test is intended to exercise the semiring structures for bitvectors
;; and checks that the expected normalizations are occuring

(defun @main () Unit
  (start start:
    (let x (fresh (Bitvector 16)))
    (let y (fresh (Bitvector 16)))
    (let z (fresh (Bitvector 16)))

    (let q1
        (+ (* (bv 16 8) x) y (bv 16 0xff) x y (* (bv 16 4) (negate x)) (bv 16 -15) (bv-and x y z))
    )
    (let q2
        (+ x y z z z)
    )

    (println "=== q1 ===")
    (println (show q1))

    (println "=== q2 ===")
    (println (show q2))

    (println "=== (+ q1 q2) ===")
    (println (show (+ q1 q2)))

    (let r1
       (bv-xor (bv-and (bv 16 8) x) y (bv 16 0xff) x y (bv-and (bv 16 1) (negate x)) (bv 16 -15) (* x y z))
    )
    (let r2
       (bv-xor x y z z z)
    )
    (println "=== r1 ===")
    (println (show r1))

    (println "=== r2 ===")
    (println (show r2))

    (println "=== (bv-xor r1 r2) ===")
    (println (show (bv-xor r1 r2)))


    (println "======")
    (println (show (bv-or x (bv-and z x y)))) ;; test absorption, should be x
    (println (show (bv-and x (bv-or z x y)))) ;; test absorption, should be x

    ;; test xor canceling, ensure that literals are recognized as part of both semiring structures
    ;; should simplify to the constant 0x33
    (println (show (+ (bv-xor x x (bv 16 42)) (bv 16 9)))) 

    ;; Demonstrates some limited distributivity
    (println (show (* (bv 16 3) y (+ x (bv 16 1)) (bv 16 9))))

    (return ())
))
