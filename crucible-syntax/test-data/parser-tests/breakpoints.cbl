(defun @foo ((n Integer)) Integer
  (registers
    ($s Integer)
    ($i Integer))
  (start begin:
    (set-register! $s 0)
    (set-register! $i 0)
    (jump header:))
  (defblock header:
    (breakpoint "foo_header" (n $s $i))
    (let i $i)
    (let c (< i n))
    (branch c body: end:))
  (defblock body:
    (breakpoint "foo_body" (n $s $i i))
    (let s $s)
    (set-register! $s (+ s i))
    (set-register! $i (+ i 1))
    (jump header:))
  (defblock end:
    (let r $s)
    (return r)))
