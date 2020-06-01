(defun @foo ((x (String Unicode))) (String Unicode)
  (start beginning:
    (print x)
    (jump next:))
  (defblock next:
    (print x)
    (return x)))

