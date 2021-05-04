(defglobal $$v (Vector Integer))
(defglobal $$ts Integer)

(defun @thread1 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$v")
    (set-global! $$v (vector 0 0 0 0 0 0 0 0))

    (funcall @write_effect "$$ts")
    (set-global! $$ts (+ 1 $$ts))

    (return ())
    )
)

(defun @main () Unit
  (start start:
    (set-global! $$ts (the Integer 0))
    (set-global! $$v (vector))
    (funcall @spawn @thread1 (to-any ()))
    (jump wait:)
  )

  (defblock wait:
    (funcall @read_effect "$$ts")
    (let last $$ts)

    (assume! (equal? $$ts 1) "progress")
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
