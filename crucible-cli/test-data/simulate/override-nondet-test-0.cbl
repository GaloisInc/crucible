(defun @main () Unit
  (start start:
    (let x (fresh Integer))
    (let y (fresh Integer))
    (let z (funcall @nondetBranchesTest 0 x y))
    (assert! (equal? z x) "should be true!")
    (return ()))
)
