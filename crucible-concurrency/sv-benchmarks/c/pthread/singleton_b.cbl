(defglobal $$v (Vector Integer))

(defun @thread1 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$v")
    (let v (fresh Integer))
    (set-global! $$v (vector-replicate 1 v))
    (return ())))

(defun @thread2 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$v")
    (set-global! $$v (vector-set $$v 0 1))
    (return ())))

(defun @thread3 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$v")
    (set-global! $$v (vector-set $$v 0 2))
    (return ())))

(defun @thread0 ((_ Any)) Unit
  (start start:
    (let t1 (funcall @spawn @thread1 (to-any ())))
    (funcall @join t1)
    (let t2 (funcall @spawn @thread2 (to-any ())))
    (let t3 (funcall @spawn @thread3 (to-any ())))
    (let t4 (funcall @spawn @thread2 (to-any ())))
    (let t5 (funcall @spawn @thread2 (to-any ())))

    (funcall @join t2)
    (funcall @join t3)
    (funcall @join t4)
    (funcall @join t5)

    (return ())))

(defun @main () Unit
  (start start:
    (let t0 (funcall @spawn @thread0 (to-any ())))
    (funcall @join t0)
    (funcall @read_effect "$$v")
    (assert! (equal? (vector-get $$v 0) 1) "Buggy!")
    ;; (assert! (or (equal? (vector-get $$v 0) 1)
    ;;              (equal? (vector-get $$v 0) 2))
    ;;              "Not Buggy!")
    (return ())))
