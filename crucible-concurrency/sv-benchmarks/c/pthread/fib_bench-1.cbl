;; Based on SV-COMP
;; https://github.com/sosy-lab/sv-benchmarks/blob/master/c/pthread/fib_bench-1.c

(defglobal $$i Integer)
(defglobal $$j Integer)

(defun @t1 ((_ Any)) Unit
  (registers
    ($k Integer))

  (start start:
    (set-register! $k 0)
    (jump header:))

  (defblock header:
    (let cond (< $k 5))
    (branch cond body: exit:))

  (defblock body:
    ;; __VERIFIER_atomic_begin()
    ;; i += j;
    ;; __VERIFIER_atomic_end()
    (funcall @write_effect "$$i-or-$$j")
    (set-global! $$i (+ $$i $$j))

    (set-register! $k (+ 1 $k))
    (jump header:)
    )

  (defblock exit:
    (return ()))
  )

(defun @t2 ((_ Any)) Unit
  (registers
    ($k Integer))

  (start start:
    (set-register! $k 0)
    (jump header:))

  (defblock header:
    (let cond (< $k 5))
    (branch cond body: exit:))

  (defblock body:
    ;; __VERIFIER_atomic_begin()
    ;; j += i;
    ;; __VERIFIER_atomic_end()
    (funcall @write_effect "$$i-or-$$j")
    (set-global! $$j (+ $$j $$i))

    (set-register! $k (+ 1 $k))
    (jump header:)
    )

  (defblock exit:
    (return ()))
  )

(defun @main () Unit
  (start start:
    (set-global! $$i 1)
    (set-global! $$j 1)

    ;; t1 executes $$i += $$j 5 times
    (funcall @spawn @t1 (to-any ()))

    ;; t2 executes $$j += $$i 5 times
    (funcall @spawn @t2 (to-any ()))

    (funcall @read_effect "$$i-or-$$j")
    (let i $$i)
    (funcall @read_effect "$$i-or-$$j")
    (let j $$j)

    (assert! (and (<= $$i 144) (<= $$j 144)) "Max value is 144")
    (return ()))
)
