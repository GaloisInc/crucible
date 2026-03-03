; Test that the error message for returning wrong type is reasonable
(defun @test () Integer
  (start block:
    (return #t)))
