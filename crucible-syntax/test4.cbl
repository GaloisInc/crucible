(defun @main ((x Integer) (y Integer)) (Vector Integer)
       (start entry:
	 (let b (fresh Bool))
         (branch b t: f:))
       (defblock t:
	 (let z0 (the (Vector Integer) (vector)))
         (let z1 (vector-cons x (vector-cons y z0)))
	 (return z1))
       (defblock f:
	 (let z2 (the (Vector Integer) (vector x)))
	 (let q1 (vector-size z2))
	 (let xalso (vector-get z2 0))
	 (let z3 (vector-set z2 0 y))
	 (return z3)))
