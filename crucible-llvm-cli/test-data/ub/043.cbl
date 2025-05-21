; Addition or subtraction of a pointer into, or just beyond, an array object and
; an integer type produces a result that does not point into, or just beyond,
; the same array object (6.5.7).

(defun @main () Unit
  (start start:
    (let p (alloca none (bv 64 1)))
    (let _ (ptr-add-offset p (bv 64 4)))
    (return ())))
