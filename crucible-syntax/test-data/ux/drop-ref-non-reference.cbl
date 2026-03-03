; Test that the error message for drop-ref on non-reference is reasonable
(defun @test () Unit
  (start block:
    (let x (the Integer 42))
    (drop-ref! x)
    (return ())))
