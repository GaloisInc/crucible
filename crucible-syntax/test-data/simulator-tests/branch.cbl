(defun @main () Unit
  (start start:
    (let p (fresh Bool))
    (let x (fresh Integer))
    (branch p t: f:))
  (defblock t:
    (output end: x))
  (defblock f:
    (output end: 12))
  (defblock (end: z Integer)
    (assert! (equal? (the Integer 42) z) "bogus condition")
    (return ()))
)
