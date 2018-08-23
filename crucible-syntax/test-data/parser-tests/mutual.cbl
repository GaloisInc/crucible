(defun @evenp ((n Integer)) Bool
  (start here:
    (let zerop (equal? n (the Integer 0)))
    (branch zerop yep: maybe:))
  (defblock maybe:
    (let next (- n 1))
    (let res (funcall @oddp next))
    (return res))
  (defblock yep:
    (let indeed #t)
    (return indeed)))

(defun @oddp ((n Integer)) Bool
  (start here:
    (let onep (equal? n 1))
    (branch onep yep: maybe:))
  (defblock maybe:
    (let next (- n 1))
    (let res (funcall @evenp next))
    (return res))
  (defblock yep:
    (let indeed #t)
    (return indeed)))

