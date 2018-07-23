(defun @f ((b Bool) (x Integer) (y Integer)) (Vector Integer)
       (start entry:
         (branch b t: f:))
       (defblock t:
	 (let z0 (vector Integer ()))
         (let z1 (vector-cons x (vector-cons y z0)))
	 (return z1))
       (defblock f:
	 (let z2 (vector Integer (x)))
	 (let q1 (vector-size z2))
	 (let xalso (vector-get z2 0))
	 (let z3 (vector-set z2 0 y))
	 (return z3)))

