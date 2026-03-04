; Test that the error message for referencing an undefined global variable is reasonable
(defun @main () Unit
  (start block:
    (set-global! @undefined-global #t)
    (return ())))
