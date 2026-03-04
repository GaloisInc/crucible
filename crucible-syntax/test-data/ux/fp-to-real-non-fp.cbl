; Test that the error message for fp-to-real on non-floating-point is reasonable
(defun @test () Real
  (start block:
    (return (fp-to-real #t))))
