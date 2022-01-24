;; Note, incomplete due to some annoying Nat/Integer mismatches in crucible-syntax

(defglobal $$SIZE Nat)
(defglobal $$table (Vector Nat))
(defglobal $$mutexes (Vector (String Unicode)))

(defun @cas ((h Nat) (val Nat) (new_val Nat)) Nat
  (start start:
    ;; Rust style: the mutex yields the resource itself.
    ;; (only yields permission to read tab[h])
    (funcall @write_effect (vector-get $$mutexes h))
    (branch (equal? val (vector-get $$table h))
            update: exit:))

  (defblock update:
    (set-global! $$table
      (vector-set $$table h new_val))
    (return 1))

  (defblock exit:
    (return 0))
)

(defun @thread_routine ((tidAny Any)) Unit
  (registers
    ($m Nat)
    ($w Nat)
    ($h Nat))

  (start start:
    (let tid  (from-just (from-any Nat tidAny) "Unpack Thread Arg"))
    (set-register! $m 0)
    (jump main_loop:))

  (defblock main_loop:
    (branch (< $m 2) adv_w: exit:))

  (defblock exit:
    (return ()))

  (defblock adv_w:
    (set-register! $m (+ $m 1))
    (set-register! $w (+ (* 11 $m) tid))
    (set-register! $h (mod (* $w 7) $$SIZE))
    (assert!
     (<= $w 2147483647) "No Overflow")
    (jump cas_loop:))

  (defblock cas_loop:
    (let ret (funcall @cas $h 0 $w))
    (branch (equal? 0 ret) again: done:))

  (defblock again:
    (set-register! $h (mod (+ 1 $h) $$SIZE))
    (jump cas_loop:))

  (defblock done:
    (return ())))



(defun @init_mutexes ((size Nat)) Unit
  (registers
    ($i Nat))

  (start start:
    (set-register! $i 0)
    (set-global! $$mutexes (vector))
    (jump loop:))

  (defblock loop:
    (let p (< $i size))
    (branch p body: done:))

  (defblock body:
    (set-global! $$mutexes
                 (vector-cons (string-concat "mutex" (show $i)) $$mutexes))
    (set-register! $i (+ 1 $i))
    (jump loop:))

  (defblock done:
    (return ()))
)
(defun @join_vector ((thids (Vector Integer))) Unit
  (registers
    ($i Nat))

  (start start:
    (set-register! $i 0)
    (jump loop:))

  (defblock loop:
    (let p (< $i (vector-size thids)))
    (branch p body: done:))

  (defblock body:
    (funcall @join (vector-get thids $i))
    (set-register! $i (+ 1 $i))
    (jump loop:))

  (defblock done:
    (return ())))

(defun @init_threads ((size Nat)) (Vector Integer)
  (registers
    ($ids (Vector Integer))
    ($i Nat))

  (start start:
    (set-register! $i 0)
    (set-register! $ids (vector))
    (jump loop:))

  (defblock loop:
    (let p (< $i size))
    (branch p body: done:))

  (defblock body:
    (let tid (funcall @spawn @thread_routine (to-any $i)))
    (set-register! $i (+ 1 $i))
    (set-register! $ids (vector-cons tid $ids))
    (jump loop:))

  (defblock done:
    (return $ids))
)

(defun @main () Unit
  (start start:
    (funcall @init_mutexes 128)
    (set-global! $$SIZE 128)
    (set-global! $$table (vector-replicate 128 (the Nat 0)))
    (let tids (funcall @init_threads 13))
    (funcall @join_vector tids)
    (return ())))
