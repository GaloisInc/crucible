(defglobal $$num Integer)


(defun @thread1 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$num")
    ;; The lock is held over the whole body, so yield just once
    (jump wait:))

  (defblock wait:
    (branch (< 0 $$num) again: done:))

  (defblock again:
    ;; Dependent with writes to "empty"
    (funcall @cond_wait "empty" "$$num")
    (jump wait:))

  (defblock done:
    (set-global! $$num (+ $$num 1))
    (funcall @cond_signal "full")
    (return ())))

(defun @thread2 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$num")
    (jump wait:))

  (defblock wait:
    (branch (equal? 0 $$num) again: done:))

  (defblock again:
    (funcall @cond_wait "full" "$$num")
    (jump wait:))

  (defblock done:
    (set-global! $$num (- $$num 1))
    (funcall @cond_signal "empty")
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$num 1)
    (let t1 (funcall @spawn @thread1 (to-any ())))
    (let t2 (funcall @spawn @thread2 (to-any ())))
    (funcall @join t1)
    (funcall @join t2)
    (assert! (equal? $$num 1) "num is one")
    (return ())))
