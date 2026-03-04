; Test that the error message for out-of-bounds bitvector select is reasonable
(defun @test () (Bitvector 8)
  (start block:
    (let x (bv 8 42))
    (return (bv-select 5 8 x))))
