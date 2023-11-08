(defun @main () Unit
  (registers
    ($i Nat)
    ($a Nat))

  (start start:
    (let x (fresh Nat))
    (set-register! $a x)
    (set-register! $i 3)
    (assume! (not (equal? x (the Nat 0))) "nonzero start")
    (jump loop:))

  (defblock loop:
    (set-register! $a (the Nat (+ $a $a)))
    (set-register! $i (- $i 1))
    (branch (equal? (the Nat 0) $i) end: loop:))

  (defblock end:
    (assert! (< (the Nat 0) $a) "nonzero")
    (return ()))
)
