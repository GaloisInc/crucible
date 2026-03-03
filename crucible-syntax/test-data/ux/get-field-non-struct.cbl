; Test that the error message for get-field on non-struct is reasonable
(defun @test () Integer
  (start block:
    (let x (the Integer 42))
    (return (get-field 0 x))))
