; Test that the error message for funcall on non-function is reasonable
(defun @main () Unit
  (start block:
    (let x (funcall #t))
    (return ())))
