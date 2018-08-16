(defun @foo ((x String)) String
  (start beginning:
    (print x)
    (jump next:))
  (defblock next:
    (print x)
    (return x)))

