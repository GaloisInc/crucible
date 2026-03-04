; Test that the error message for invalid bitvector zero extension is reasonable
(defun @test () (Bitvector 8)
  (start block:
    (let x (bv 16 42))
    (return (zero-extend 8 x))))
