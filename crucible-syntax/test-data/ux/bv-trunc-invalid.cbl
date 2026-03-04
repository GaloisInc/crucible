; Test that the error message for invalid bitvector truncation is reasonable
(defun @test () (Bitvector 16)
  (start block:
    (let x (bv 8 42))
    (return (bv-trunc 16 x))))
