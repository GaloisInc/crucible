(defun @main () Unit
  (start start:
    (let x (fresh Integer))
    (let y (fresh Integer))
    (let z (funcall @symbolicBranchesTest x y))
    (assert! (equal? z x) "bogus!")
    (return ()))
)
