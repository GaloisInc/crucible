;; This test is intended to exercise the normilization structures
;; for boolean values

(defun @main () Unit
  (start start:
     (let x (fresh Bool))
     (let y (fresh Bool))
     (let z (fresh Bool))
     (let w (fresh Bool))

     (let q1 (and x y z y z))

     (println "=== q1 ===")
     (println (show q1))

     (println "=== (or q1 y) ===")
     (println (show (or q1 y)))

     (println "=== (or q1 (or y z)) ===")
     (println (show (or q1 (or y z))))

     (println "=== (and q1 y) ===")
     (println (show (and q1 y)))

     (println "=== (and q1 (not y)) ===")
     (println (show (and q1 (not y))))

     (println "=== (or (not q1) y) ===")
     (println (show (or (not q1) y)))

     (println "=== (or q1 (not y)) ===")
     (println (show (or q1 (not y))))

     (println "====== expect single n-ary connective")
     (println (show (and (not (or x y)) (not (or z w)))))
     (println (show (or (not (and x y)) (not (and z w)))))
     (println (show (or (not (and x y)) (or z w))))
     (println (show (or (or z w) (not (and x y)))))

     
     ;; pretty subtle absorption step here, can reduce to (or z w)
     (println "====== expect absorption to (or z w)")
     (println (show (or (or z w) (not (or x (not w))))))

     (return ())
))
