; Test that the error message for inj with wrong type context is reasonable
(defun @test () Integer
  (start block:
    (return (inj 0 42))))
