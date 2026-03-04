; Test that the error message for abs on unsupported type is reasonable
(defun @test () Nat
  (start block:
    (return (abs 1))))
