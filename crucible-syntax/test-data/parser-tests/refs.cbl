(defun @refs ((s String)) (Ref String)
  (start st:
    (let x (ref s))
    (let y (deref x))
    (set-ref! x (string-append y s))
    (drop-ref! x)
    (return x)))
