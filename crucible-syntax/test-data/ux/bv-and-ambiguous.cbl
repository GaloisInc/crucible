; Test that the error message for ambiguous bv-and width is reasonable
(defun @test () Unit
  (start block:
    (let x (bv-and))
    (return ())))
