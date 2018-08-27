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
    (set-register! $a (+ $a $a))
    (set-register! $i (- $i 1))
    (let a-mod-6 (the Nat (mod $a 6)))
    (branch (equal? (the Nat 0) a-mod-6) err: next:))

  (defblock next:
    (branch (equal? (the Nat 0) $i) end: loop:))

  (defblock end:
    (assert! (< (the Nat 0) $a) "nonzero")
    (return ()))

  (defblock err:
    (error "oopsie!"))
)
