(defglobal $$counter Integer)
(defun @main () Unit
  (start start:
    (set-global! $$counter 0)
    (let y (funcall @spawn @t1 (to-any ())))
    (funcall @join 1)

    (funcall @read_effect "$$counter")
    (assert! (equal? $$counter 1) "Thread 1 definitely done")
    (return ())))
(defun @t1 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$counter")
    (set-global! $$counter 1)
    (return ())))
