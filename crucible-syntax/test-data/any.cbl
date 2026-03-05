(defun @main ((x Integer)) (Maybe Integer)
  (start go:
    (let a (to-any x))
    (let b (from-any Integer a))
    (return b)))
