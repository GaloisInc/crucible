(defglobal $$lock1 Bool) ;; #t -> free
(defglobal $$lock2 Bool) ;; #t -> free
(defglobal $$counter Integer)

(defun @acquire1 () Unit
  (start start:
    (funcall @write_effect_cond_set "lock1" (vector-cons "lock1" (vector)))
    (set-global! $$lock1 #f) ;; Lock is not free
    (return ())))

(defun @release1 () Unit
  (start start:
    (funcall @write_effect "lock1")
    (assert! (not $$lock1) "lock1 not held")
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
    (assert! (not $$lock2) "lock2 not held")
    (set-global! $$lock2 #t) ;; Lock is free
    (return ())))

(defun @producer ((_ Any)) Unit
  (registers ($batch Integer))

  (start start:
    (funcall @acquire2)
    (funcall @acquire1)
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
    (set-register! $fairness 2)
    (jump loop:))

  (defblock loop:
    (assume! (<= 0 $fairness) "Don't starve here")
    (funcall @acquire1)
    (funcall @read_effect "counter")
    (branch (< 0 $$counter) loop_done: loop_cont:))
  (defblock loop_cont:
    (set-register! $fairness (- $fairness 1))
    (funcall @release1)
    (jump loop:))

  (defblock loop_done:
    (funcall @write_effect "counter")
    (set-global! $$counter (- $$counter 1))

    (funcall @read_effect "counter")
    (assert! (<= 0 $$counter) "counter >= 0")
    (funcall @release1)
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$counter 0)
    (set-global! $$lock1  #t)
    (set-global! $$lock2  #t)

    ;; Reordering these can seriously alter the number of executions explored
    ;; (move consumers before producers). Possibly because we're doing extremely
    ;; basic DPOR without sleep sets? (plus an artifact of how we initially
    ;; explore threads of course)
    (funcall @spawn @consumer (to-any ()))
    (funcall @spawn @consumer (to-any ()))
    (funcall @spawn @producer (to-any ()))
    (funcall @spawn @producer (to-any ()))
    (return ())))
