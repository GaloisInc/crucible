(defglobal $$lock1 Bool) ;; #t -> free
(defglobal $$lock2 Bool) ;; #t -> free
(defglobal $$counter Integer)

(defun @acquire1 ((who (String Unicode))) Unit
  (start start:
    (funcall @write_effect_cond_set "lock1" (vector-cons "lock1" (vector)))
    (assert! $$lock1 "lock1 free (b)")
    (set-global! $$lock1 #f) ;; Lock is not free
    (return ())))

(defun @release1 () Unit
  (start start:
    (funcall @write_effect "lock1")
    ;; (assert! (not $$lock1) "lock1 not free (b)")
    (set-global! $$lock1 #t) ;; Lock is free
    (return ())))

(defun @acquire2 () Unit
  (start start:
    (funcall @write_effect_cond_set "lock2" (vector-cons "lock2" (vector)))
    (set-global! $$lock2 #f) ;; Lock is not free
    (return ())))

(defun @release2 () Unit
  (start start:
    (funcall @write_effect "lock2")
    (set-global! $$lock2 #t) ;; Lock is free
    (return ())))

(defun @producer ((arg Any)) Unit
  (registers ($batch Integer))

  (start start:
    (let tid (show (from-just (from-any Integer arg) "Cast input")))
    (funcall @acquire2)
    (funcall @acquire1 tid)
    (funcall @write_effect "counter")
    (set-register! $batch 1) ;; This is non-det in original
    (branch (< 0 $$counter) pos_counter: zero_counter:))

  (defblock pos_counter:
    (funcall @write_effect "counter")
    (set-global! $$counter (+ $$counter 1))
    (funcall @release1)
    (funcall @release2)
    (return ()))

  (defblock zero_counter:
    (funcall @release1)
    (funcall @write_effect "counter")
    (set-global! $$counter 0)
    (jump loop:))

  (defblock loop:
    (branch (< 0 $batch) loop_body: loop_done:))

  (defblock loop_body:
    (funcall @write_effect "counter")
    (set-global! $$counter (+ $$counter 1))
    (set-register! $batch (- $batch 1))
    (jump loop:))

  (defblock loop_done:
    (funcall @write_effect "counter")
    (set-register! $batch $$counter)
    (funcall @release2)
    (return ())))

(defun @consumer ((_ Any)) Unit
  (registers ($fairness Integer))
  (start start:
    (set-register! $fairness 1)
    (jump loop:))

  (defblock loop:
    (assume! (<= 0 $fairness) "Don't starve here")
    (funcall @acquire1 "consumer")
    (funcall @read_effect "counter")
    (branch (< 0 $$counter) loop_done: loop_cont:))
  (defblock loop_cont:
    (set-register! $fairness (- $fairness 1))
    (funcall @release1)
    (jump loop:))

  (defblock loop_done:
    (funcall @write_effect "counter")
    (set-global! $$counter (- $$counter 1))

    ;; (funcall @read_effect "counter")
    (funcall @release1)
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$counter 0)
    (set-global! $$lock1  #t)
    (set-global! $$lock2  #t)
    (let h (funcall @spawn @producer (to-any (the Integer 1))))
    (let h1 (funcall @spawn @consumer (to-any ())))
    (funcall @join h)
    (funcall @join h1)
    (return ())))
