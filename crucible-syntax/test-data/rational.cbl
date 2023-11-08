;; exercise all of the real-constructing operations

(defun @test-rational () Real
  (start start:
    (let v (the Real 0x0f/45))
    (let x (the Real (/ v 2/1)))
    (let a (+ (mod 1/2 3/2) 22))
    (let intp (integer? a))
    (let y (+ x v 0xff 33/2))
    (let z (- x v))
    (let w (* y z))
    (let q (/ y z))
    (let m (mod y z))

    (let p1 (equal? x y))
    (let p2 (< x y))
    (let p3 (<= x y))
    (let p (and p1 p2 p3))
    (let r (if p w q))
    (return r)))
