(defglobal $$r Integer)
(defglobal $$s Integer)

(defun @thr1 ((_ Any)) Unit
  (registers ($l Integer) ($max Integer))
  (start start:
    (set-register! $l 0)
    (set-register! $max 5)
    (funcall @write_effect "r")
    (set-global! $$r (+ 1 $$r))
    (branch (equal? $$r 1) loop: exit:))
  (defblock loop:
    (set-register! $max (- $max 1))
    (funcall @write_effect "s")
    (set-global! $$s (+ 1 $$s))
    (set-register! $l (+ 1 $l))
    (assert! (equal? $$s $l) "Only one writer")
    (branch (<= 0 $max) loop: exit:))
  (defblock exit:
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$r 0)
    (set-global! $$s 0)
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (return ())))
