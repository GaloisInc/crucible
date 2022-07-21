(defun @main () Integer
  (start start:
    (let x (fresh Integer))
    (let y (fresh Integer))
    (let z (funcall @notdetBranchesTest 1 x y))
    (assert! (equal? z y) "should be true!")
    (return z))
)