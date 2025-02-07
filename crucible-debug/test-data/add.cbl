(defun @add ((x Integer) (y Integer)) Integer
  (start start:
    (return (+ x y))))

(defun @main () Unit
  (start start:
    (let _ (funcall @add 2 3))
    (return ())))
