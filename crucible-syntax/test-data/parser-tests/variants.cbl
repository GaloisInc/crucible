(defun @rot-cases ((t (Variant Integer Bool String))) (Variant Bool String Integer)
  (start go:
    (case t
      int:
      bool:
      string:))
  (defblock (int: x Integer)
    (let i (the (Variant Bool String Integer) (inj 2 x)))
    (return i))
  (defblock (bool: y Bool)
    (let b (the (Variant Bool String Integer) (inj 0 y)))
    (return b))
  (defblock (string: z String)
    (let s (the (Variant Bool String Integer) (inj 1 z)))
    (return s)))
