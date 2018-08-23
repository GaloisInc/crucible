(defun @main () Unit
  (start start:
    (let p (fresh Bool))
    (let x (fresh Real))
    (branch p t: f:))
  (defblock t:
    (output next: (just x)))
  (defblock f:
    (output next: nothing))
  (defblock (next: z (Maybe Real))
    (let q (from-just z "OK to project z"))
    (assert! (equal? x (+ q 1)) "from-just eq (bogus)")
    (return ()))
)
