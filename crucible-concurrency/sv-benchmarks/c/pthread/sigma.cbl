(defglobal $$array    (Vector Integer))
(defglobal $$arrayRes (Vector (String Unicode)))
(defglobal $$arrayIdx Nat)

(defun @thread ((_ Any)) Unit
  (start start:
    (funcall @read_effect "$$arrayIdx")
    (let i (- $$arrayIdx 1))

    (funcall @write_effect (vector-get $$arrayRes i))
    (set-global! $$array (vector-set $$array i 1))
    (return ())))

(defun @initializeRes ((k Nat)) Unit
  (registers
    ($i Nat))

  (start start:
    (set-register! $i 0)
    (set-global! $$arrayRes (vector))
    (jump loop:))

  (defblock loop:
    (branch (< $i k) body: done:))

  (defblock body:
    (set-global! $$arrayRes (vector-cons (string-concat "res" (show $i)) $$arrayRes))
    (set-register! $i (+ 1 $i))
    (jump loop:))

  (defblock done:
    (return ())))

(defun @main () Unit
  (registers
    ($sum Integer)
    ($tids (Vector Integer))
    ($tid Nat))

  (start start:
    (let sizeNat (the Nat     4))
    (let sizeInt (the Integer 4))
    (funcall @initializeRes sizeNat)
    (set-global! $$array (vector-replicate sizeNat 0))
    (set-global! $$arrayIdx 0)
    (set-register! $tids (vector))
    (set-register! $tid 0)
    (set-register! $sum 0)
    (jump loop:))

   (defblock loop:
     (branch (< $tid sizeNat) body: join:))

   (defblock body:
     (funcall @write_effect "$$arrayIdx")
     (set-global! $$arrayIdx (+ 1 $$arrayIdx))
     (let tid (funcall @spawn @thread (to-any ())))
     (set-register! $tids (vector-cons tid $tids))
     (set-register! $tid (+ 1 $tid))
     (jump loop:))

   (defblock join:
     (set-register! $tid 0)
     (jump join_loop:))

   (defblock join_loop:
     (branch (< $tid sizeNat) join_body: sum:))

   (defblock join_body:
     (funcall @join (vector-get $tids $tid))
     (set-register! $tid (+ 1 $tid))
     (jump join_loop:))

   (defblock sum:
     (set-register! $tid 0)
     (jump sum_loop:))

   (defblock sum_loop:
     (branch (< $tid sizeNat) sum_body: exit:))

   (defblock sum_body:
     (set-register! $sum (+ $sum (vector-get $$array $tid)))
     (set-register! $tid (+ 1 $tid))
     (jump sum_loop:))

   (defblock exit:
     (assert! (<= $sum sizeInt) "Should be false")
     (return ())))
