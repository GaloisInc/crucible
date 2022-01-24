(defglobal $$dummy (Ref Integer))
(defglobal $$counter (Ref Integer))

(defun @main () Unit
  (start start:
    (let x (the Integer 0))
    (let a (ref x))
    (let b (ref x))
    (set-global! $$counter a)
    (set-global! $$dummy b)
    (let y (funcall @spawn @t1 (to-any ())))
    (let z (funcall @spawn @t2 (to-any ())))

    (funcall @join y)
    (funcall @join z)
    (funcall @write_effect_ref (to-any $$dummy))

    ;; Yield is required before a global action
    (funcall @write_effect_ref (to-any $$counter))
    (let p (< 0 (deref $$counter)))

    (assert! p "Positive counter")
    (return ()))
)

(defun @t1 ((_ Any)) Unit
  (start start:
    (funcall @inc 1)
    (return ()))
)
(defun @t2 ((_ Any)) Unit
  (start start:
    (funcall @inc 2)
    (return ()))
)

(defun @inc ((who Integer)) Unit
  (start start:
    (funcall @write_effect_ref (to-any $$counter))
    (let y (+ (deref $$counter) 1))
    (set-ref! $$counter y)
    (return ()))
)
