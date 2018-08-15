;; exercise all of the integer-constructing operations

(defun @test-integer () Integer
  (start start:
    (let q (the Integer (negate 2)))
    (let v (the Integer 0x0f))
    (let x (the Integer (/ v 2)))
    (let y (the Integer (* x q)))
    (let r (the Integer (+ (mod x 5) 22)))
    (let ra (the Integer (abs r)))
    (let z  (the Integer (- y ra)))
    (let p1 (< x y))
    (let p2 (<= x y))
    (let p3 (equal? x y))
    (let p (and p1 (and p2 p3)))
    (let za (if p q v))
    (return za)))
