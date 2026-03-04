; Test that the error message for show on unsupported type is reasonable
(defun @test () (String Unicode)
  (start block:
    (let x (the (Vector Integer) (vector)))
    (return (show x))))
