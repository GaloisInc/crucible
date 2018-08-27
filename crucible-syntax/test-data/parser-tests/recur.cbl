(defun @fact ((n Integer)) Integer
  (start at-the-beginning:
    (let donep (< n 1))
    (branch donep recur: done:))
  (defblock recur:
    (let next (funcall @fact (- n 1)))
    (let val (the Integer (* next n)))
    (return val))
  (defblock done:
    (let init (the Integer 1))
    (return init)))
