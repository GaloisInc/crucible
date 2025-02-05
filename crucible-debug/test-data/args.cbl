(defun @add ((x Integer) (y Integer)) Integer
  (start start:
    (return (+ x y))))

(defun @main () Unit
  (start start:
    (let p (fresh Bool))
    (let x (fresh Integer))
    (branch p t: f:))
  (defblock t:
    (output end: x))
  (defblock f:
    (output end: 12))
  (defblock (end: z Integer)
    (funcall @add 0 z)
    (return ())))
