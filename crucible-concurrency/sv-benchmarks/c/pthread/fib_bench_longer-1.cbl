;; Based on SV-COMP
;; https://github.com/sosy-lab/sv-benchmarks/blob/master/c/pthread/fib_bench-1.c

;; TODO: data race detection?

(defglobal $$i Integer)
(defglobal $$j Integer)

(defun @t1 ((_ Any)) Unit
  (registers
    ($k Integer))

  (start start:
    (set-register! $k 0)
    (jump header:))

  (defblock header:
    (let cond (< $k 6))
    (branch cond body: exit:))

  (defblock body:
    ;; This is atomic in the original program
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
    (let cond (< $k 6))
    (branch cond body: exit:))

  (defblock body:
    ;; This is atomic in the original program
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

    (funcall @spawn @t1 (to-any ()))
    (funcall @spawn @t2 (to-any ()))

    (funcall @read_effect "$$i-or-$$j")
    (let condI (< 377 $$i))

    (funcall @read_effect "$$i-or-$$j")
    (let condJ (< 377 $$j))

    (branch (or condI condJ) error: done:)
  )

  (defblock error:
    (error "Not reachable?"))

  (defblock done:
    (return ())
    )
)
