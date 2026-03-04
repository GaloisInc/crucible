; Test that the error message for ubv-to-fp on non-bitvector is reasonable
(defun @test () (FP Double)
  (start block:
    (return (ubv-to-fp Double rne #t))))
