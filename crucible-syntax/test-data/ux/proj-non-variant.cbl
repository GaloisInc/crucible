; Test that the error message for proj on non-variant is reasonable
(defun @test () Integer
  (start block:
    (let x (the Integer 42))
    (return (proj 0 x))))
