(defun @a () Unit
  (start start:
    (let br (funcall @b))
    (return br)))

(defun @b () Unit
  (start start:
    (let cr (funcall @c))
    (return cr)))

(defun @c () Unit
  (start start:
    (return ())))
