(defun @foo ((x (String Unicode))) (String Unicode)
  (registers
    ($out (String Unicode))
    ($count Integer))
  (start beginning:
    (print x)
    (set-register! $out x)
    (set-register! $count 3)
    (jump loop:))
  (defblock loop:
    (let c $count)
    (set-register! $count (- c 1))
    (let out $out)
    (set-register! $out (string-concat out x))
    (let go (< c 0))
    (branch go loop: done:))
  (defblock done:
    (let val $out)
    (return val)))
