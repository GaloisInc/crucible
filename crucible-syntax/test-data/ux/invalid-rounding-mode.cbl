; Test that the error message for an invalid rounding mode is reasonable
(defun @test () Unit
  (start block:
    (let r (fresh Real))
    (let f (real-to-fp Float invalid-mode r))
    (return ())))
