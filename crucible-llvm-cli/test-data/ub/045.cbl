; Pointers that do not point into, or just beyond, the same array object are
; subtracted (6.5.7).

(defun @main () Unit
  (start start:
    (let p (alloca none (bv 64 1)))
    (let q (alloca none (bv 64 1)))
    (let _ (ptr-sub p q))
    (return ())))
