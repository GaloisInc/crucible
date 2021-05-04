(defglobal $$counter Integer)
(defglobal $$mutex Bool) ;; #t --> available

(defun @main () Unit
  (start start:
    (let x (the Integer 0))
    (set-global! $$counter x)

    (set-global! $$mutex #t) ;; Mutex starts out available

    (let t1 (funcall @spawn @t1 (to-any ())))
    (let t2 (funcall @spawn @t1 (to-any ())))

    (funcall @lock)
    (funcall @read_effect "$$counter")
    (let p (equal? (mod $$counter 2) 0))
    (assert! p "Even counter")
    (funcall @unlock)
    (return ()))
)

(defun @t1 ((_ Any)) Unit
  (start start:
    (funcall @lock)
    (funcall @inc)
    (funcall @inc)
    (funcall @unlock)
    (return ())))

(defun @inc () Unit
  (start start:
    (funcall @write_effect "$$counter")
    (let y (+ $$counter 1))
    (set-global! $$counter y)
    (return ())))

(defun @lock() Unit
  (start start:
    (funcall @write_effect_cond_set "mutex" (vector-cons "mutex" (vector)))
    (assert! $$mutex "Mutex is free!")
    (set-global! $$mutex #f)
    (return ())))

(defun @unlock() Unit
  (start start:
    (assert! (not $$mutex) "Mutex is held!")
    (set-global! $$mutex #t)
    (return ())))
