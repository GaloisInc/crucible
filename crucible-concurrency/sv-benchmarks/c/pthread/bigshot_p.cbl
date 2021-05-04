;; Based on SV-COMP
;; https://github.com/sosy-lab/sv-benchmarks/blob/master/c/pthread/bigshot_p.c

(defglobal $$v (Vector Integer)) ;; A string of integers

(defun @thread1 ((_ Any)) Unit
;;v = calloc(8, sizeof(char));
  (start start:
    (funcall @write_effect "$$v")
    (set-global! $$v (vector 0 0 0 0 0 0 0 0))
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
    (return ()))
)

(defun @main () Unit
;;  pthread_t t1, t2;
;;
;;  pthread_create(&t1, 0, thread1, 0);
;;  pthread_create(&t2, 0, thread2, 0);
;;  pthread_join(t1, 0);
;;  pthread_join(t2, 0);
;;
;;  __VERIFIER_assert(!v || v[0] == 'B');
  (start start:
    (set-global! $$v (vector))
    (let tid1 (funcall @spawn @thread1 (to-any ())))
    (let tid2 (funcall @spawn @thread2 (to-any ())))
    (jump wait:)
  )

  ;; Thread join
  (defblock wait:
    (funcall @join tid1)
    (funcall @join tid2)
    (jump done:)
  )

  (defblock done:
    (funcall @read_effect "$$v")
    (let vempty (vector-empty? $$v))

    (funcall @read_effect "$$v")
    (let v0     (vector-get $$v 0))

    (assert! (or vempty (equal? v0 1)) "ASDF")
    (return ())
    )
)
