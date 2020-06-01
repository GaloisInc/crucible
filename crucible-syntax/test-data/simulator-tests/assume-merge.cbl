(defun @main () Unit
  (start start:
    (let x (fresh Integer))
    (branch (<= (the Integer 0) x) pos: neg:))
  (defblock pos:
    (assume! (equal? (the Integer 0) (the Integer (mod x 2))) "even")
    (jump end:))
  (defblock neg:
    (assume! (equal? (the Integer 1) (the Integer (mod x 2))) "odd")
    (jump end:))
  (defblock end:
    (error "oopsie!"))
)
