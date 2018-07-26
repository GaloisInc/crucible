(defun @main () Integer
  (registers
    ($val Integer))

  (start entry:
     ;; (let b #t)
     (let b (fresh Bool))
     (let x (fresh Integer))
     (let y (fresh Integer))
     (set-register! $val 42)
     (branch b t: f:))
  (defblock t:
    (let b2 (fresh Bool))
    (branch b2 tf: ret:))

  (defblock f:
    (let zf (the Integer (+ y 2)))
    (set-register! $val zf)
    (jump ret:))

  (defblock tt:
    (let ztt (the Integer (+ x y)))
    (set-register! $val ztt)
    (jump ret:))

  (defblock tf:
    (let ztf (the Integer (+ x (+ y 1))))
    (set-register! $val ztf)
    (jump ret:))

  (defblock ret:
    (let r $val)
    (return r))
)
