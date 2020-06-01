(defun @test-natural () Nat
  (start start:
    (let x (the Nat 5))
    (let y (the Nat 10))
    (let z (+ x 7))
    (let s (- z y))
    (let w (/ x y))
    (let q (mod x y))

    (let p1 (equal? x z))
    (let p2 (< x y))
    (let p3 (<= z 20))
    (let p (and p1 p2 p3))
    (let r (if p s q))
    (return r)))
