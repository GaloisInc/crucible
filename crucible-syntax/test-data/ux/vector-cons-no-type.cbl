; Test that the error message for vector-cons without type is reasonable
(defun @test () Unit
  (start block:
    (let y (vector-cons #t (vector-lit)))
    (return ())))
