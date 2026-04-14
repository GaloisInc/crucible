;; Test unique concretization

(defun @main () Unit
  (start start:
    (let x (fresh Integer))
    (let y (fresh Integer))
    ;; Constrain x to be uniquely 42
    (assume! (equal? x (the Integer 42)) "x is 42")
    ;; y is unconstrained -- multiple values are possible
    (funcall @uniquely-conc-ints x y)
    ;; Now constrain y too
    (assume! (equal? y (the Integer 7)) "y is 7")
    (funcall @uniquely-conc-ints x y)
    (return ())))
