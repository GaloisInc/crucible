; Test that the error message for invalid struct index is reasonable
(defun @test () Integer
  (start block:
    (let x (struct (the Integer 42) #t))
    (return (get-field 5 x))))
