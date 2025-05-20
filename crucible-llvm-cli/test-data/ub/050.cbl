; Pointers that do not point to the same aggregate or union (nor just beyond the
; same array object) are compared using relational operators (6.5.9).

(defun @main () Unit
  (start start:
    (let p (alloca none (bv 64 1)))
    (let q (alloca none (bv 64 1)))
    (let _ (ptr-le p q))
    (return ())))
