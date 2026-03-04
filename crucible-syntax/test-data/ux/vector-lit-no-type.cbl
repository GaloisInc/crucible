; Test that the error message for vector-lit without type is reasonable
(defun @test () Unit
  (start block:
    (let x (vector-lit))
    (return ())))
