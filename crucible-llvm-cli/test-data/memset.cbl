(defun @main () Unit
  (start start:
    (let g (resolve-global "memset"))
    (let h (load-handle (Ptr 64) ((Ptr 64) (Ptr 32) (Ptr 64)) g))

    (let p (alloca none (bv 64 8)))
    (let c (ptr 32 0 (bv 32 0)))
    (let sz (ptr 64 0 (bv 64 4)))
    (let _ (funcall h p c sz))

    (return ())))