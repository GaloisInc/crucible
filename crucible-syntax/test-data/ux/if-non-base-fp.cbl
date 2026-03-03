; Test that the error message for if branches with non-base/FP type is reasonable
(defun @test () (Vector Integer)
  (start block:
    (let x (the (Vector Integer) (vector)))
    (let y (the (Vector Integer) (vector)))
    (return (if #t x y))))
