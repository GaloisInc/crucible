; Test that the error message for string-concat on non-string is reasonable
(defun @test () (String Unicode)
  (start block:
    (return (string-concat "hello" #t))))
