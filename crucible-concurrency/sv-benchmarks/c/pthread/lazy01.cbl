(defglobal $$data Integer)

(defun @thread1 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "data")
    (set-global! $$data (+ 1 $$data))
    (return ())))

(defun @thread2 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "data")
    (set-global! $$data (+ 2 $$data))
    (return ())))

(defun @thread3 ((_ Any)) Unit
  (start start:
    (funcall @read_effect "data")
    (let d $$data)
    (assert! (<= d 3) "data > 3 ==> error") ;; Right
    ;; (assert! (< d 3) "data >= 3 ==> error")    ;; Wrong
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$data 0)
    (let t1 (funcall @spawn @thread1 (to-any ())))
    (let t2 (funcall @spawn @thread2 (to-any ())))
    (let t3 (funcall @spawn @thread3 (to-any ())))
    (funcall @join t1)
    (funcall @join t2)
    (funcall @join t3)
    (return ())))
