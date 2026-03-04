(defun @main ((x Integer)) (Maybe Integer)
  (start go:
    (let n (the (Maybe Integer) nothing))
    (let j (just x))
    (let v (from-just j "not nothing"))
    (return n)))
