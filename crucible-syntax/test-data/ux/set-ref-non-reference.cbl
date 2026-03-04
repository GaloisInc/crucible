; Test that the error message for set-ref on non-reference is reasonable
(defun @test () Unit
  (start block:
    (let x (the Integer 42))
    (set-ref! x 10)
    (return ())))
