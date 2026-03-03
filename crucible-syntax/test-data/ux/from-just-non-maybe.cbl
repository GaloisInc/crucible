; Test that the error message for from-just on non-Maybe is reasonable
(defun @test () Integer
  (start block:
    (return (from-just #t "not a maybe"))))
