; Test that the error message for bv-nonzero on non-bitvector is reasonable
(defun @test () Bool
  (start block:
    (return (bv-nonzero #t))))
