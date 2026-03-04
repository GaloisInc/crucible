; Test that the error message for jumping to an undefined label is reasonable
(defun @test () Unit
  (start block:
    (jump unknown-label)))
