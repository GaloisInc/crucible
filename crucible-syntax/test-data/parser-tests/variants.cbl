(defun @rot-cases ((t (Variant Integer Bool (String Unicode))))
                   (Variant Bool (String Unicode) Integer)
  (start go:
    (case t
      int:
      bool:
      string:))
  (defblock (int: x Integer)
    (let i (the (Variant Bool (String Unicode) Integer) (inj 2 x)))
    (return i))
  (defblock (bool: y Bool)
    (let b (the (Variant Bool (String Unicode) Integer) (inj 0 y)))
    (let b1 (from-just (proj 0 b) "proj0"))
    (let b2 (from-just (proj 1 b) "proj1"))
    (let b3 (from-just (proj 2 b) "proj2"))
    (return b))
  (defblock (string: z (String Unicode))
    (let s (the (Variant Bool (String Unicode) Integer) (inj 1 z)))
    (return s)))
