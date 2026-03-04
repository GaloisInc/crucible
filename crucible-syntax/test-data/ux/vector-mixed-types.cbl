; Test that a vector literal with mixed element types is rejected
(defun @test () (Vector Integer)
  (start block:
    (let v (the (Vector Integer) (vector (the Integer 1) #t)))
    (return v)))
