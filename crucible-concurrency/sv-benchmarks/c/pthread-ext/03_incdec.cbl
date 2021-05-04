(defglobal $$value (Bitvector 2))
(defglobal $$m Bool)
(defglobal $$incr Bool)
(defglobal $$decr Bool)

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

(defun @inc () Unit
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
    (funcall @write_effect_set (vector-cons "value" (vector-cons "incr" (vector))))
    (set-global! $$incr #t)
    (set-global! $$value (+ (bv 2 1) $v))
    (funcall @release) ;; Move this to the beginning of the block to see a bug!
    (funcall @write_effect_set (vector-cons "value" (vector-cons "decr" (vector))))
    (assert! (or $$decr (< $v $$value)) "Strictly increased value")
    (return ())))

(defun @dec () Unit
  (registers ($v (Bitvector 2)))

  (start start:
    (set-register! $v (bv 2 0))
    (funcall @acquire)
    (funcall @read_effect "value")
    (branch (equal? $$value (bv 2 0)) neg: not_neg:))

  (defblock neg:
    (funcall @release)
    (return ()))

  (defblock not_neg:
    (funcall @read_effect "value")
    (set-register! $v $$value)
    (funcall @write_effect_set (vector-cons "value" (vector-cons "decr" (vector))))
    (set-global! $$decr #t)
    (set-global! $$value (- $v (bv 2 1)))
    (funcall @release) ;; Move this to the beginning of the block to see a bug!
    (funcall @write_effect_set (vector-cons "value" (vector-cons "incr" (vector))))
    (assert! (or $$incr (< $$value $v)) "Strictly decreased value")
    (return ())))

(defun @thr1 ((_ Any)) Unit
  (start start:
    (let incr_or_decr (fresh Bool))
    (branch incr_or_decr incr: decr:))

  (defblock incr:
    (funcall @inc)
    (return ()))

  (defblock decr:
    (funcall @dec)
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$m #t)
    (set-global! $$incr #f)
    (set-global! $$decr #f)
    (set-global! $$value (bv 2 0))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))

    (return ())))
