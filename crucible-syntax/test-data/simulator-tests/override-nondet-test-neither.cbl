(defun @main () Integer
  (start start:
    (let w (fresh Integer))
    (let x (fresh Integer))
    (let y (fresh Integer))
    (assume! (and (not (equal? w 0)) (not (equal? w 1))) "w is not 0 or 1")
    (let z (funcall @nondetBranchesTest w x y))
    (return z))
)