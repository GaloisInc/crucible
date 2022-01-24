(defglobal $$FAILED Nat)
(defglobal $$next_ticket Nat)
(defglobal $$now_serving Nat)
(defglobal $$c Nat)

(defun @NEXT ((e Nat)) Nat
  (start start:
    (return (mod (+ e 1) $$FAILED))))

(defun @fetch_and_increment__next_ticket () Nat
  (start start:
    (funcall @write_effect_set
      (vector-cons "next_ticket" (vector-cons "now_serving" (vector))))
    (let nxt (funcall @NEXT $$next_ticket))
    (branch (equal? nxt $$now_serving) eq: not_eq:))
  (defblock eq:
    (return $$FAILED))
  (defblock not_eq:
    (let val $$next_ticket)
    (set-global! $$next_ticket nxt)
    (return val)))

(defun @acquire_lock () Unit
  (registers ($fairness Integer))
  (start start:
    (set-register! $fairness 2)
    (let my_ticket (funcall @fetch_and_increment__next_ticket))
    (assume! (not (equal? $$FAILED my_ticket)) "reached limit")
    (jump loop:))
  (defblock loop:
    (assume! (<= 0 $fairness) "progress please")
    (set-register! $fairness (- $fairness 1))
    (funcall @read_effect "now_serving")
    (branch (equal? $$now_serving my_ticket) done: loop:))
  (defblock done:
    (return ())))

(defun @release_lock () Unit
  (start start:
    (funcall @write_effect "now_serving")
    (set-global! $$now_serving (+ $$now_serving 1))
    (return ())))

(defun @thr1 ((_ Any)) Unit
  (start start:
     (funcall @acquire_lock)
     (funcall @write_effect "c")
     (set-global! $$c (+ $$c 1))
     (assert! (equal? $$c 1) "Only one writer")
     (set-global! $$c (- $$c 1))
     (funcall @release_lock)
     (return ())))


(defun @main () Unit
  (start start:
    (set-global! $$c 0)
    (set-global! $$FAILED 3)
    (set-global! $$next_ticket 0)
    (set-global! $$now_serving 0)

    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (return ())))
