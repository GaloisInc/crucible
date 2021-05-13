(defglobal $$counter Integer)
(defglobal $$ts Integer)

(defun @main () Unit
  (registers
    ($count Integer))
  (start start:
    (set-register! $count 0)
    (let x (the Integer 0)) ;; (fresh Integer))
    (set-global! $$counter x)
    (set-global! $$ts (the Integer 0))
    (let y (funcall @spawn @t1 (to-any ())))
    (let z (funcall @spawn @t2 (to-any ())))
    (jump loop:))

  (defblock loop:
    (funcall @write_effect "$$ts")
    (let again (and (< $$ts 2) (< $count 1)))
    (set-register! $count (+ $count 1))
    (branch again loop: done:))

  (defblock done:
    (funcall @write_effect "$$counter")
    (let p (< 0 $$counter))
    (assert! p "Positive counter")
    (return ()))
)

(defun @t1 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$counter")
    (let p (< 0 $$counter))
    (assert! (equal? 0 $$counter) "Bad assertion, admittedly")
    (branch p t: f:))
  (defblock t:
    (output end: 2))
  (defblock f:
    (output end: 3))
  (defblock (end: z Integer)
    (funcall @write_effect "$$counter")
    (set-global! $$counter z)
    (funcall @write_effect "$$ts")
    (set-global! $$ts (+ 1 $$ts))
    (return ())) 
)

(defun @t2 ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$counter")
    (let p (< 0 $$counter))
    (branch p t: f:))
  (defblock t:
    (output end: 2))
  (defblock f:
    (output end: 3))
  (defblock (end: z Integer)
    (funcall @write_effect "$$counter")
    (set-global! $$counter z)
    (funcall @write_effect "$$ts")
    (set-global! $$ts (+ 1 $$ts))
    (return ())) 
)
