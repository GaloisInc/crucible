; Test that the error message for fresh with non-base type is reasonable
(defun @main () Unit
  (start block:
    (let x (fresh (Vector Bool)))
    (return ())))
