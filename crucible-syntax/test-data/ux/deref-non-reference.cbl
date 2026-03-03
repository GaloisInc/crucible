; Test that the error message for deref of non-reference type is reasonable
(defun @test () Integer
  (start block:
    (let x (the Integer 42))
    (return (deref x))))
