;; exercise all of the boolean-constructing operations

(defun @test-bool () Bool
  (start start:
    (let x #t)
    (let y #f)
    (let z (and (and x y) #f))
    (let q (or #t (or x y)))
    (let w (if q (not z) y))
    (let r (equal? (xor z w) q))
    (return r)))
