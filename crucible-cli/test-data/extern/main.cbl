(extern $$foo Integer)

(defun @main () Unit
  (start start:
    (assert! (equal? $$foo 42) "$$foo equals 42")
    (return ()))
)
