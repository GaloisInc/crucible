(declare @foo () Integer)

(defun @main () Unit
  (start start:
    (let foo-res (funcall @foo))
    (assert! (equal? foo-res 42) "@foo returns 42")
    (return ()))
)
