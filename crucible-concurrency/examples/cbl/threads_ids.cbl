(defglobal $$counter Integer)

(defun @main () Unit
  (start start:
    (let x (the Integer 0))
    (set-global! $$counter x)
    (let y (funcall @spawn @t1 (to-any ())))
    (let w (funcall @spawn @t2 (to-any ())))

    ;; Yield is required before a global action
    (funcall @write_effect "$$counter")
    (let p (< 0 $$counter))

    (assert! p "Positive counter")
    (return ()))
)

(defun @t1 ((_ Any)) Unit
  (start start:
    (funcall @inc 1)
    (jump t:))

  (defblock t:
    (funcall @inc 1)
    (return ()))
)

(defun @t2 ((_ Any)) Unit
  (start start:
    (funcall @inc 2)
    (jump t:))

  (defblock t:
    (funcall @inc 2)
    (return ()))
)

(defun @inc ((who Integer)) Unit
  (start start:
    ;; Yield is required before a global action
    (funcall @write_effect "$$counter")
    (let y (+ $$counter 1))

    ;; Yield is required before a global action
    (funcall @write_effect "$$counter")
    (set-global! $$counter y)

    (return ())))
