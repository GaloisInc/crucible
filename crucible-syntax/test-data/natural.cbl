(defun @test-natural () Nat
  (start start:
    (let x (the Nat 5))
    (let y (the Nat 10))
    (let z (the Nat (+ x 7)))
    (let s (the Nat (- z y)))
    (let w (the Nat (/ x y)))
    (let q (the Nat (mod x y)))

    (let p1 (equal? x z))
    (let p2 (< x y))
    (let p3 (<= z (the Nat 20)))
    (let p (and p1 (and p2 p3)))
    (let r (if p s q))
    (return r)))
