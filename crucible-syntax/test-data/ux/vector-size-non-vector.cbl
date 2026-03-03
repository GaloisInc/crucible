; Test that the error message for vector-size on non-vector is reasonable
(defun @test () Nat
  (start block:
    (return (vector-size #t))))
