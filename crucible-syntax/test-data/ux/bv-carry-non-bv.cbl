; Test that the error message for bv-carry on non-bitvector is reasonable
(defun @test () Bool
  (start block:
    (return (bv-carry #t #f))))
