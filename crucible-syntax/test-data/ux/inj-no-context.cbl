; Test that the error message for inj without variant context is reasonable
(defun @test () Unit
  (start block:
    (let x (inj 0 42))
    (return ())))
