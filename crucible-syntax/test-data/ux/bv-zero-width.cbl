; Test that a bitvector literal with width 0 is rejected
(defun @test () (Bitvector 0)
  (start block:
    (return (bv 0 0))))
