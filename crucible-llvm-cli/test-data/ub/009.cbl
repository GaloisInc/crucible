; An object is referred to outside of its lifetime (6.2.4).

(defun @do-alloc () (Ptr 64)
  (start start:
    (push-frame "do-alloc")
    (let p (alloca none (bv 64 1)))
    (pop-frame)
    (return p)))

(defun @main () Unit
  (start start:
    (let p (funcall @do-alloc))
    (let z (ptr 8 0 (bv 8 0)))
    (store none i8 p z)
    (return ())))
