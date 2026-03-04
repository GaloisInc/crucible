; Test that the error message for an unknown register name is reasonable
(defun @main () Unit
  (registers)
  (start block:
    (let x $reg)
    (return ())))
