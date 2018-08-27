
(defglobal $$counter Integer)

(defun @count () Integer
  (registers ($n Integer))
  (start begin:
    (set-global! $$counter 0)
    (set-register! $n 5)
    (jump loop:))
  (defblock loop:
    (let n $n)
    (set-register! $n (- n 1))
    (let c $$counter)
    (set-global! $$counter (+ c 2))
    (let n* $n)
    (let donep (< n* 0))
    (branch donep done: loop:))
  (defblock done:
    (let res $$counter)
    (return res)))
