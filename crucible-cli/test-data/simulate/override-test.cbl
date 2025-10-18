(defun @main () Unit
  (start start:
    (let p (fresh Bool))
    (let x (fresh Integer))
    (let y (fresh Integer))
    (let z (funcall @symbolicBranchTest p x y))
    (assert! (equal? z (if p x y)) "should be true!")
    (return ()))
)
