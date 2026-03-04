; Test that the error message for literal of wrong type is reasonable
(defun @test () Integer
  (start block:
    (return (the Integer "hello"))))
