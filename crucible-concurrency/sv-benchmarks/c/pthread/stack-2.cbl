;; Global State:
(defglobal $$top Nat)
(defglobal $$flag Bool)
(defglobal $$arr (Vector Integer))

;; A constant:
(defglobal $$SIZE Nat)


(defun @inc_top () Unit
  (start start:
    (set-global! $$top (+ 1 $$top))
    (return ())))

(defun @dec_top () Unit
  (start start:
    (set-global! $$top (- $$top 1))
    (return ())))

(defun @stack_empty () Bool
  (start start:
    (return (equal? $$top 0))))

(defun @push ((x Integer)) Unit
  (start start:
    (assert! (< $$top $$SIZE) "Overflow!")
    (set-global! $$arr (vector-set $$arr $$top x))
    (funcall @inc_top)
    (return ())))

(defun @pop () Integer
  (start start:
    (assert! (< 0 $$top) "Underflow!")
    (funcall @dec_top)
    (return (vector-get $$arr $$top))))

(defun @t1 ((_ Any)) Unit
  (registers
    ($i Nat))

  (start start:
    (set-register! $i 0)
    (jump header:))

  (defblock header:
    (branch (< $i $$SIZE) body: done:))

  (defblock body:
    (funcall @write_effect "$$m")
    (let tmp (fresh Integer)) ;; Original program assumes tmp < SIZE, but this never matters?
    (funcall @push tmp)
    (set-global! $$flag #t)
    (set-register! $i (+ $i 1))
    (jump header:))

  (defblock done:
    (return ())))

(defun @t2 ((_ Any)) Unit
  (registers
    ($i Nat))

  (start start:
    (set-register! $i 0)
    (jump header:))

  (defblock header:
    (branch (< $i $$SIZE) body: done:))

  (defblock body:
    (funcall @write_effect "$$m")
    (set-register! $i (+ $i 1))
    (branch $$flag pop: header:))

  (defblock pop:
    (funcall @pop)
    (jump header:))

  (defblock done:
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$flag #f)
    (set-global! $$top 0)
    (set-global! $$SIZE 5)
    (set-global! $$arr (vector-replicate $$SIZE 0))

    (let t1 (funcall @spawn @t1 (to-any ())))
    (let t2 (funcall @spawn @t2 (to-any ())))

    (funcall @join t1)
    (funcall @join t2)

    (return ())))
