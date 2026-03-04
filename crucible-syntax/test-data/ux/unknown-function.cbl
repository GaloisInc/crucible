; Test that the error message for an unknown function name is reasonable
(defun @main () Unit
  (start block:
    (let result @foo)
    (return ())))
