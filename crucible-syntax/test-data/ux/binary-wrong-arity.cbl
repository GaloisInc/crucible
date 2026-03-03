; Test that the error message for binary operator with wrong arity is reasonable
(defun @test () Integer
  (start block:
    (return (- 1 2 3))))
