(defglobal $$N Integer)
(defglobal $$s Integer)
(defglobal $$t Integer)

(defun @inct () Unit
  (start start:
    (funcall @write_effect "t")
    (set-global! $$t (+ 1 $$t))
    (return ())))

(defun @incs () Unit
  (start start:
    (funcall @write_effect "s")
    (set-global! $$s (+ 1 $$s))
    (return ())))

(defun @th ((_ Any)) Unit
  (start start:
    (funcall @inct)
    (funcall @write_effect_set (vector-cons "s" (vector-cons "t" (vector))))
    (assert! (< $$s $$t) "True by some kind of counting argument")
    (funcall @incs)
    (return ())))

(defun @main () Unit
  (registers ($i Integer))
  (start start:
    (set-global! $$s 0)
    (set-global! $$t 0)
    (set-global! $$N 4)
    (set-register! $i 0)
    (jump loop:))

  (defblock loop:
    (branch (< $i $$N) loop_body: done:))
  (defblock loop_body:
    (set-register! $i (+ 1 $i))
    (funcall @spawn @th (to-any ()))
    (jump loop:))

  (defblock done:
    (return ())))
