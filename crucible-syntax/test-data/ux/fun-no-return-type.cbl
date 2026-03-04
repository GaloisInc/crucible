; Test that the error message for function type with no return type is reasonable
(defun @test () Unit
  (start block:
    (let x (Fun) @test)
    (return ())))
