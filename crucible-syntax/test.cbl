(defun @f ((x Integer) (y Integer)) Integer
       (start entry:
         (jump hello:))
       (defblock hello:
	 (let z (* x y))
	 (return z)))

