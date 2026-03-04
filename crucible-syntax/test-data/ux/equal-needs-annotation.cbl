; Test that the error message for equal? needing type annotation is reasonable
(defun @test () Bool
  (start block:
    (return (equal? 1 2))))
