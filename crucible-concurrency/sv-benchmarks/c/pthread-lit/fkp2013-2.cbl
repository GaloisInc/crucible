(defglobal $$x Integer)
(defglobal $$N Integer)

(defun @thr1 ((_ Any)) Unit
  (start start:
    (funcall @read_effect "x")
    (assert! (<= $$x $$N) "max x")
    (return ())))

(defun @thr2 ((_ Any)) Unit
  (start start:
    (funcall @read_effect "x")
    (let t $$x)
    (funcall @write_effect "x")
    (set-global! $$x (+ t 1))
    (return ())))

(defun @main () Unit
  (registers ($i Integer))
  (start start:
    (set-global! $$x 0)
    (set-global! $$N 3)
    (set-register! $i 0)
    (funcall @spawn @thr1 (to-any ()))
    (jump loop:))

  (defblock loop:
    (branch (< $i $$N) loop_body: done:))
  (defblock loop_body:
    (set-register! $i (+ 1 $i))
    (funcall @spawn @thr2 (to-any ()))
    (jump loop:))

  (defblock done:
    (return ())))
