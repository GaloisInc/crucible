; Test that the error message for setting an unknown global is reasonable
(defun @main () Unit
  (start block:
    (set-global! $$g #t)
    (return ())))
