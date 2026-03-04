; Test that the error message for overloaded expression without annotation is reasonable
(defun @test () Unit
  (start block:
    (let z (+ 1 2))
    (return ())))
