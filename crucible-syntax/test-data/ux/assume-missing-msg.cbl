; Test that assume! with missing message argument is rejected
(defun @test () Unit
  (start block:
    (assume! #f)
    (return ())))
