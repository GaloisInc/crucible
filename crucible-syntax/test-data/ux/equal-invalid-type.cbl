; Test that the error message for equality test on invalid type is reasonable
(defun @test () Bool
  (start block:
    (let x (to-any #t))
    (let y (to-any #f))
    (return (equal? x y))))
