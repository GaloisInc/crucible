(defglobal $$c Integer)
(defglobal $$lock (Ref Integer))

(defun @tas ((v (Ref Integer)) (o (Ref Integer))) Unit
  (start start:
    (funcall @write_effect_ref
      (to-any (vector-cons (to-any v)
              (vector-cons (to-any o) (the (Vector Any) (vector))))))
    (let dv (deref v))
    (set-ref! o dv)
    (set-ref! v 1)
    (return ())))

(defun @acquire () Unit
  (registers ($delay (Bitvector 8)) ($cond (Ref Integer)) ($fairness Integer))
  (start start:
    (set-register! $fairness 2)
    (set-register! $delay (bv 8 1))
    (let pz (ref (the Integer 0)))
    (set-register! $cond pz)
    (funcall @tas $$lock $cond)
    (jump loop:))
  (defblock loop:
    (assume! (<= 0 $fairness) "Progress please")
    (set-register! $fairness (- $fairness 1))
    (branch (equal? 1 (deref $cond)) body: done:))
  (defblock body:
    (set-register! $delay (if (< $delay (* (bv 8 2) $delay)) (* (bv 8 2) $delay) $delay))
    (funcall @tas $$lock $cond)
    (jump loop:))
  (defblock done:
    (funcall @read_effect "lock")
    (assert! (not (equal? (deref $cond) (deref $$lock))) "Got the lock")
    (return ())))

(defun @release () Unit
  (start start:
    (funcall @read_effect "lock")
    (assert! (not (equal? (deref $$lock) 0)) "Release locked lock")
    (funcall @write_effect_ref (to-any (vector-cons (to-any $$lock) (the (Vector Any) (vector)))))
    (set-ref! $$lock 0)
    (return ())))

(defun @thr1 ((_ Any)) Unit
  (start start:
     (funcall @acquire)
     (funcall @write_effect "c")
     (set-global! $$c (+ $$c 1))
     (assert! (equal? $$c 1) "Only one writer")
     (set-global! $$c (- $$c 1))
     (funcall @release)
     (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$c 0)
    (let lockinit (ref (the Integer 0)))
    (set-global! $$lock lockinit)
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (funcall @spawn @thr1 (to-any ()))
    (return ())))
