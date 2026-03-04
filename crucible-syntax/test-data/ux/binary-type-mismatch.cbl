; Test that the error message for binary operator type mismatch is reasonable
(defun @test () Integer
  (start block:
    (return (+ 1 #t))))
