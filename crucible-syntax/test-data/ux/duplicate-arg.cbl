; Test that the error message for duplicate function arguments is reasonable
(defun @foo ((x Integer) (y Bool) (x Integer)) Unit
  (start block:
    (return ())))
