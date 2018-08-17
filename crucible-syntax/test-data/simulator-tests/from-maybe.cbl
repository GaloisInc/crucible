(defun @main () Unit
  (start start:
    (let p (fresh Bool))
    (let x (fresh Real))
    (branch p t: f:))
  (defblock t:
    (output next: (the (Maybe Real) (just x))))
  (defblock f:
    (output next: (the (Maybe Real) nothing)))
  (defblock (next: z (Maybe Real))
    (let q (the Real (from-just z "OK to project z")))
    (assert! (equal? x (the Real (+ q 1))) "from-just eq (bogus)")
    (return ()))
)
