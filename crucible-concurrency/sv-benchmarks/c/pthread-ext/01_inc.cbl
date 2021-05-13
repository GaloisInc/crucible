(defglobal $$value (Bitvector 2))
(defglobal $$m Bool)

(defun @acquire () Unit
  (start start:
    (funcall @write_effect_cond_set "m" (vector-cons "m" (vector)))
    (set-global! $$m #f)
    (return ())))

(defun @release () Unit
  (start start:
    (funcall @write_effect "m")
    (assert! (not $$m) "is held")
    (set-global! $$m #t)
    (return ())))

(defun @thr1 ((_ Any)) Unit
  (registers ($v (Bitvector 2)))

  (start start:
    (set-register! $v (bv 2 0))
    (funcall @acquire)
    (funcall @read_effect "value")
    (branch (equal? $$value (- (bv 2 0) (bv 2 1))) neg: not_neg:))

  (defblock neg:
    (funcall @release)
    (return ()))

  (defblock not_neg:
    (funcall @read_effect "value")
    (set-register! $v $$value)
    (funcall @write_effect "value")
    (set-global! $$value (+ (bv 2 1) $v))
    (funcall @release) ;; Move this to the beginning of the block to see a bug!
    (funcall @read_effect "value")
    (assert! (< $v $$value) "Strictly increased value")
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$m #t)
    (set-global! $$value (bv 2 0))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))

    (return ())))
