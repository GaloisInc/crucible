;; Based on SV-COMP
;; https://github.com/sosy-lab/sv-benchmarks/blob/master/c/pthread/bigshot_s2.c

(defglobal $$v (Vector Integer)) ;; A string of integers
(defglobal $$ts Integer)         ;; Thread termination counter

(defun @thread1 ((_ Any)) Unit
;;v = calloc(8, sizeof(char));
  (start start:
    (funcall @write_effect "$$v")
    (set-global! $$v (vector 0 0 0 0 0 0 0 0))

    (funcall @write_effect "$$ts")
    (set-global! $$ts (+ 1 $$ts))
    (return ())
    )
)

(defun @thread2 ((_ Any)) Unit
;; if (v) strcpy(v, "Bigshot");
  (start start:
    (funcall @read_effect "$$v")
    (let leave (vector-empty? $$v))
    (branch leave quit: write:))

  (defblock write:
    (funcall @write_effect "$$v")
    (set-global! $$v (vector 1 2 3 4 5 6 7 8))
    (jump quit:))

  (defblock quit:
    (funcall @write_effect "$$ts")
    (set-global! $$ts (+ 1 $$ts))
    (return ()))
)

(defun @main () Unit
;;  pthread_t t1, t2;
;;
;;  pthread_create(&t1, 0, thread1, 0);
;;  pthread_join(t1, 0);
;;  pthread_create(&t2, 0, thread2, 0);
;;  pthread_join(t2, 0);
;;
;;  __VERIFIER_assert(v[0] == 'B'); // malloc can fail, but not in SV-COMP
  (start start:
    (set-global! $$ts (the Integer 0))
    (set-global! $$v (vector))

    (let tid1 (funcall @spawn @thread1 (to-any ())))
    (funcall @join tid1)

    (let tid2 (funcall @spawn @thread2 (to-any ())))
    (funcall @join tid2)
    (jump done:)
  )

  (defblock done:
    (funcall @read_effect "$$v")
    (let v0     (vector-get $$v 0))

    (assert! (equal? v0 1) "ASDF")
    (return ())
    )
)
