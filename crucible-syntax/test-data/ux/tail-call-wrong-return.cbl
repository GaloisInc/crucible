; Test that the error message for tail-call with wrong return type is reasonable
(declare @other () Integer)

(defun @test () Bool
  (start block:
    (tail-call @other)))
