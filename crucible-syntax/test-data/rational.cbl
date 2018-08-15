;; exercise all of the real-constructing operations

(defun @test-rational () Real
  (start start:
    (let v (the Real 0x0f/45))
    (let x (the Real (/ v 2/1)))
    (let a (the Real (+ (mod 1/2 3/2) 22)))
    (let intp (integer? a))
    (let y (the Real (+ x v)))
    (let z (the Real (- x v)))
    (let w (the Real (* y z)))
    (let q (the Real (/ y z)))
    (let m (the Real (mod y z)))

    (let p1 (equal? x y))
    (let p2 (< x y))
    (let p3 (<= x y))
    (let p (and p1 (and p2 p3)))
    (let r (if p w q))
    (return r)))
