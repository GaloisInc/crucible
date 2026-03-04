; Test that the error message for bitvector width mismatch is reasonable
(defun @test () (Bitvector 8)
  (start block:
    (let x (bv 8 42))
    (let y (bv 16 100))
    (return (bv-and x y))))
