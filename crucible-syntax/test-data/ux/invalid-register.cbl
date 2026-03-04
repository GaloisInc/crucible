; Test that the error message for invalid register specification is reasonable
(defun @foo () Unit
  (registers
    (notaregister Integer))
  (start block:
    (return ())))
