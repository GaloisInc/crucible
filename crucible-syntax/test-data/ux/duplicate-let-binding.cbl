; Test that the error message for duplicate let binding is reasonable
(defun @test () Integer
  (start block:
    (let x (the Integer 42))
    (let x (the Integer 10))
    (return x)))
