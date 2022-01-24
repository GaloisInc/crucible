;; Based on the ring library from
;; sv-benchmarks/blob/master/c/pthread-divine/ring.h
(defglobal $$SIZE Nat)
(defglobal $$CNT Nat)
(defglobal $$K Nat) ;; Progress param

(defglobal $$pwriter (Ref Nat))
(defglobal $$preader (Ref Nat))
(defglobal $$pq (Ref (Vector Nat)))

(defglobal $$mutex Bool)

(defun @lock() Unit
  (start start:
    (funcall @write_effect_cond_set "mutex" (vector-cons "mutex" (vector)))
    (assert! $$mutex "Mutex is free!")
    (set-global! $$mutex #f)
    (return ())))

(defun @unlock() Unit
  (start start:
    (assert! (not $$mutex) "Mutex is held!")
    (set-global! $$mutex #t)
    (return ())))


(defun @ring_enqueue
       ((pwriter (Ref Nat)) (preader (Ref Nat)) (pq (Ref (Vector Nat))) (x Nat))
       Unit
  (registers ($progress Nat))
  (start start:
    (set-register! $progress 0)
    (jump wait_loop:))

  (defblock wait_loop:
    (funcall @write_effect_ref
      (to-any (vector-cons (to-any pwriter)
              (vector-cons (to-any preader)
              (vector-cons (to-any pq) (the (Vector Any) (vector)))))))
    (let w (deref pwriter))
    (let r (deref preader))
    ;; For fairness:
    (assume! (< $progress $$K) "Progress please!")
    (set-register! $progress (+ $progress 1))
    (branch (equal? (mod (+ 1 w) $$SIZE) r) wait_loop: continue:))

  (defblock continue:
    (funcall @write_effect_ref
      (to-any (vector-cons (to-any pwriter)
              (vector-cons (to-any pq) (the (Vector Any) (vector))))))
    (let where (deref pwriter))
    (set-ref! pq (vector-set (deref pq) where x))
    (funcall @write_effect_ref
      (to-any pwriter))
    (set-ref! pwriter (mod (+ (deref pwriter) 1) $$SIZE))
    (return ())))

(defun @ring_dequeue
       ((pwriter (Ref Nat)) (preader (Ref Nat)) (pq (Ref (Vector Nat))))
       Nat
  (start start:
    (funcall @write_effect_ref
      (to-any (vector-cons (to-any preader)
              (vector-cons (to-any pq) (the (Vector Any) (vector))))))
    (let x (vector-get (deref pq) (deref preader)))
    (funcall @write_effect_ref
      (to-any preader))
    (set-ref! preader (mod (+ (deref preader) 1) $$SIZE))
    (return x)))

(defun @ring_empty
       ((pwriter (Ref Nat)) (preader (Ref Nat)) (pq (Ref (Vector Nat))))
       Bool
  (start start:
    (funcall @write_effect_ref
      (to-any (vector-cons (to-any preader)
              (vector-cons (to-any pwriter) (the (Vector Any) (vector))))))
    (return (equal? (deref preader) (deref pwriter)))))

(defun @ring_init
       ((pwriter (Ref Nat)) (preader (Ref Nat)) (pq (Ref (Vector Nat))))
       Unit
  (start start:
    (funcall @write_effect_ref
      (to-any (vector-cons (to-any preader)
              (vector-cons (to-any pwriter) (the (Vector Any) (vector))))))
    (set-ref! preader 0)
    (set-ref! pwriter 0)
    (return ())))

(defun @writer_fn
       ((pwriter (Ref Nat)) (preader (Ref Nat)) (pq (Ref (Vector Nat))))
       Unit
  (registers ($i Nat))
  (start start:
    (set-register! $i 0)
    (jump loop:))

  (defblock body:
    (funcall @lock)
    (funcall @ring_enqueue $$pwriter $$preader $$pq (+ 1 $i))
    (funcall @unlock)
    (set-register! $i (+ $i 1))
    (jump loop:))

  (defblock loop:
    (branch (< $i $$CNT) body: done:))

  (defblock done:
    (return ())))

(defun @reader_maybe_buggy ((arg Any)) Unit
  (registers ($val Nat) ($last Nat) ($i Nat) ($progress Nat))
  (start start:
    (let buggy (from-just (from-any Bool arg) "arg is bool"))
    (set-register! $val 0)
    (set-register! $last 0)
    (set-register! $i 0)
    (set-register! $progress 0)
    (jump loop:))

  (defblock loop:
    (branch (< $i $$CNT) body: done:))

  (defblock body:
    (assume! (< $progress $$K) "Progress please!")
    (set-register! $progress (+ 1 $progress))
    (branch buggy do_dequeue: check_empty:))

  (defblock check_empty:
    (let emp (funcall @ring_empty $$pwriter $$preader $$pq))
    (branch emp loop: do_dequeue:))

  (defblock do_dequeue:
    (let res (funcall @ring_dequeue $$pwriter $$preader $$pq))
    (set-register! $val res)
    (assert! (equal? $val (+ 1 $last)) "Should fail")
    (set-register! $last $val)
    (set-register! $i (+ $i 1))
    (jump loop:))

  (defblock done:
    (assert! (equal? $last $$CNT) "Assertion on loop?")
    (let isemp (funcall @ring_empty $$pwriter $$preader $$pq))
    (assert! isemp "Should be empty")
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$mutex #t) ;; Initially "free"
    (set-global! $$SIZE 4)
    (set-global! $$CNT 8)
    (set-global! $$K 2)
    (let w (ref (the Nat 0)))
    (let r (ref (the Nat 0)))
    (set-global! $$pwriter w)
    (set-global! $$preader r)
    (let q (ref (vector-replicate $$SIZE (the Nat 0))))
    (set-global! $$pq q)

     ;; #t --> buggy
     ;; #f --> not buggy
    (let rdr (funcall @spawn @reader_maybe_buggy (to-any #t)))
    (funcall @writer_fn $$pwriter $$preader $$pq)

    (funcall @join rdr)
    (return ())))
