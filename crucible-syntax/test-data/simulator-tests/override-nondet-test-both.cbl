(defun @main () Integer
  (start start:
    (let w (fresh Integer))
    (let x (fresh Integer))
    (let y (fresh Integer))
    (assume! (or (equal? w 0) (equal? w 1)) "w is 0 or 1")
    (let z (funcall @nondetBranchesTest w x y))
    (assert! (or (equal? z x) (equal? z y)) "should be true!")
    (assert! (or (equal? x y) (not (and (equal? z x) (equal? z y)))) "should be true!")
    (return z))
)