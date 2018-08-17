(defun @main () Integer
  (start start:
    (let a (fresh Integer))
    (let b (fresh Integer))
    (branch (equal? a (the Integer 5)) l1: end:))
  (defblock l1:
    (branch (<= (the Integer 0) b) l2: end:))
  (defblock l2:
    (assert! (equal? a (the Integer 5)) "assert")
    (jump end:))
  (defblock end:
    (return 0))
)
