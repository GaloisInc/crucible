; The value of an object with automatic storage duration is used while the
; object has an indeterminate representation (6.2.4, 6.7.11, 6.8).

(defun @main () Unit
  (start start:
    (let p (alloca none (bv 64 1)))
    (load none i8 p)
    (return ())))
