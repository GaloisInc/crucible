(defglobal $$counter Integer)

(defun @main () Unit
  (start start:
    (let x (the Integer 0))
    (set-global! $$counter x)
    (let y (funcall @spawn @t1 (to-any ())))
    (let w (funcall @spawn @t2 (to-any ())))
    (funcall @write_effect "$$counter")
    (let p (< 0 $$counter))
    (assert! p "Positive counter")
    (return ()))
)

(defun @t1 ((_ Any)) Unit
  (start start:
    (funcall @inc)
    (jump t:))
  (defblock t:
    (funcall @inc)
    (return ()))
)

(defun @t2 ((_ Any)) Unit
  (start start:
    (funcall @inc)
    (jump t:))
  (defblock t:
    (funcall @inc)
    (return ()))
)

(defun @inc () Unit
  (start start:
    (funcall @write_effect "$$counter")
    (let y (+ $$counter 1))
    (set-global! $$counter y)
    (return ())))
