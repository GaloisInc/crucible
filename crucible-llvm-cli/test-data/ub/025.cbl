; A pointer is used to call a function whose type is not compatible with the
; referenced type (6.3.2.3).

(defun @main () Unit
  (start start:
    (let g (resolve-global "malloc"))
    (let h (load-handle Unit () g))
    (funcall h)
    (return ())))
