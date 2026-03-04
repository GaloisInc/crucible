; Test that the error message for nothing without type is reasonable
(defun @test () Unit
  (start block:
    (let x (nothing))
    (return ())))
