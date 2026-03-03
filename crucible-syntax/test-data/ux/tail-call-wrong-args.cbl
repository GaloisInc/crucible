; Test that the error message for tail-call with wrong argument types is reasonable
(declare @other ((x Integer)) Unit)

(defun @test () Unit
  (start block:
    (tail-call @other #t)))
