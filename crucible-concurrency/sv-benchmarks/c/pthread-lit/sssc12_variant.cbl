;; Note, $$len is never written, so for simplicity it's just treated as a constant
(defglobal $$len Nat)
(defglobal $$next Nat)
(defglobal $$data (Vector Nat))

(defun @thr ((_ Any)) Unit
  (registers ($c Nat) ($end Nat))

  (start start:
    ;; c = 0;
    (set-register! $c 0)
    ;; end = 0;
    (set-register! $end 0)

    ;; if (next + 10 <= len) ...
    (funcall @write_effect "$$next")
    (branch (<= (+ $$next 10) $$len) incr: loop:))

  ;; (then)
  (defblock incr:
    ;; c = next;
    (set-register! $c $$next)
    ;; next = end = next + 10;
    (set-register! $end (+ $$next 10))
    (set-global! $$next $end)
    (jump loop:))

  (defblock loop:
    (branch (< $c $end) body: done:))

  (defblock body:
    (funcall @write_effect (string-concat "$$data" (show $c)))
    (set-global! $$data (vector-set $$data $c 0))
    (funcall @write_effect (string-concat "$$data" (show $c)))
    (set-global! $$data (vector-set $$data $c 1))
    (funcall @read_effect (string-concat "$$data" (show $c)))
    (assert! (equal? (vector-get $$data $c) 1) "Thread touch distinct data")
    (set-register! $c (+ $c 1))
    (jump loop:))

  (defblock done:
    (return ())))

(defun @main () Unit
  (start start:
    (let len (the Nat 40)) ;; (fresh Nat) isn't possible, can't have symbolic vector length
    (set-global! $$len len)
    (set-global! $$next 0)
    (set-global! $$data (vector-replicate $$len 0))
    (funcall @spawn @thr (to-any ()))
    (funcall @spawn @thr (to-any ()))
    (funcall @spawn @thr (to-any ()))
    (funcall @spawn @thr (to-any ()))
    ; (funcall @spawn @thr (to-any ()))
    ; (funcall @spawn @thr (to-any ()))
    (return ())))
