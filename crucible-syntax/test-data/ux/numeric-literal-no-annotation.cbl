; Test that the error message for numeric literal without annotation is reasonable
(defun @test () Unit
  (start block:
    (let x 42)
    (return ())))
