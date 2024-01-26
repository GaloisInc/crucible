;; exercise all of the integer-constructing operations

(defun @test-integer () Integer
  (start start:
    (let q (the Integer (negate 2)))
    (let v (the Integer 0x0f))
    (let x (/ v 2))
    (let y (* x q))
    (let r (+ (mod x 5) -4))
    (let ra (abs r))
    (let z  (- y ra))
    (let p1 (< x y))
    (let p2 (<= x y))
    (let p3 (equal? x y))
    (let p (and p1 p2 p3))
    (let za (if p q v))
    (let neg-one (the Integer -1))
    (return za)))
