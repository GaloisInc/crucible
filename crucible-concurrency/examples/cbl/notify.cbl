(defglobal $$g Integer)

(defun @t1 ((_ Any)) Unit
  (start start:
     (funcall @read_effect "$$g")
     (branch (< 0 $$g) done: wait:))

  (defblock wait:
     (funcall @read_effect "c")
     (funcall @cond_wait "c" "$$g")

     (funcall @read_effect "$$g")
     (assert! (< 0 $$g) "condition true")
     (jump done:))

  (defblock done:
     (return ())))

(defun @t2 ((_ Any)) Unit
  (start start:
     (funcall @write_effect "$$g")
     (set-global! $$g 1)
     (return ())))

(defun @main () Unit
  (start start:
    (let v (fresh Integer))
    (set-global! $$g (the Integer 0))
    (let t1 (funcall @spawn @t1 (to-any ())))
    (let t2 (funcall @spawn @t2 (to-any ())))
    (funcall @join t2)

    (funcall @write_effect "c")
    (funcall @cond_signal "c")

    (funcall @join t1)
    (return ())))
