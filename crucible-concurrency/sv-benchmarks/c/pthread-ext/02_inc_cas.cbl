(defglobal $$value (Bitvector 2))

(defun @cas_value ((e (Bitvector 2)) (u (Bitvector 2))) Bool
  (start start:
    (funcall @write_effect "value")
    (branch (equal? $$value e) eq: not_eq:))

  (defblock eq:
    (set-global! $$value u)
    (return #t))

  (defblock not_eq:
    (return #f)))


(defun @thr1 ((_ Any)) Unit
  (registers ($v (Bitvector 2))
             ($vn (Bitvector 2))
             ($casret Bool))

  (start start:
    (set-register! $v (bv 2 0))
    (set-register! $vn (bv 2 0))
    (jump do_while:))

  (defblock do_while:
    (funcall @read_effect "value")
    (set-register! $v $$value)
    (branch (equal? $v (- (bv 2 0) (bv 2 1))) neg: not_neg:))

  (defblock neg:
    (return ()))

  (defblock not_neg:
    (set-register! $vn (+ $v (bv 2 1)))
    (let r (funcall @cas_value $v $vn))
    (branch r done: do_while:))

  (defblock done:
    (funcall @read_effect "value")
    (assert! (< $v $$value) "No overflow")
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$value (bv 2 0))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    ; (funcall @spawn @thr1 (to-any ()))
    ; (funcall @spawn @thr1 (to-any ()))

    (return ())))
