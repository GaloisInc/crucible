; Test that the error message for unary operator with wrong arity is reasonable
(defun @test () Bool
  (start block:
    (return (not #t #f))))
