; Test that the error message for less-than on unsupported type is reasonable
(defun @test () Bool
  (start block:
    (return (< #t #f))))
