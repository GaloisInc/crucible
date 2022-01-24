(defglobal $$data1 Integer)
(defglobal $$data2 Integer)

(defun @funcA ((_ Any)) Unit
  (start start:
    (funcall @write_effect "data1")
    (set-global! $$data1 1)

    (funcall @write_effect "data1")
    (let p $$data1)

    (funcall @write_effect "data2")
    (set-global! $$data2 (+ 1 p))
    (return ())))

(defun @funcB ((_ Any)) Unit
  (registers ($t1 Integer) ($t2 Integer))

  (start start:
    (set-register! $t1 -1)
    (set-register! $t2 -1)

    (funcall @write_effect "data1")
    (branch (equal? 0 $$data1) done: continue:))

    (defblock continue:
      (set-register! $t1 $$data1)

      (funcall @write_effect "data2")
      (set-register! $t2 $$data2)

      (assert! (equal? $t2 (+ 1 $t1)) "Wrong?")
      (jump done:))

   (defblock done:
    (return ())))

(defun @init_threads ((th (-> Any Unit)) (size Integer)) (Vector Integer)
  (registers
    ($ids (Vector Integer))
    ($i Integer))

  (start start:
    (set-register! $i 0)
    (set-register! $ids (vector))
    (jump loop:))

  (defblock loop:
    (let p (< $i size))
    (branch p body: done:))

  (defblock body:
    (let tid (funcall @spawn th (to-any ())))
    (set-register! $i (+ 1 $i))
    (set-register! $ids (vector-cons tid $ids))
    (jump loop:))

  (defblock done:
    (return $ids))
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

(defun @main () Unit
  (start start:
    (set-global! $$data1 0)
    (set-global! $$data2 0)
    (let tthreads (funcall @init_threads @funcA 2))
    (let rthreads (funcall @init_threads @funcB 1))
    (funcall @join_vector tthreads)
    (funcall @join_vector rthreads)
    (return ())))
