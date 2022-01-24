(defglobal $$data1 Integer)
(defglobal $$data2 Integer)

(defun @thread1 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "data1")
    (set-global! $$data1 (+ 1 $$data1))

    (funcall @write_effect "data2")
    (set-global! $$data2 (+ 1 $$data2))

    (return ())))

(defun @thread2 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "data1")
    (set-global! $$data1 (+ 5 $$data1))

    (funcall @write_effect "data2")
    (set-global! $$data2 (- $$data2 6))

    (return ())))

(defun @main () Unit
  (start start:

    (set-global! $$data1 10)
    (set-global! $$data2 10)

    (let t1 (funcall @spawn @thread1 (to-any ())))
    (let t2 (funcall @spawn @thread2 (to-any ())))

    (funcall @join t1)
    (funcall @join t2)

    (assert! (or (equal? $$data1 16) (equal? $$data2 5)) "This succeeds")

    (return ())))
