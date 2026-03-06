; Test that case with too many labels is rejected
(defun @test () Integer
  (start block:
    (let x (the (Variant Integer) (inj 0 (the Integer 1))))
    (case x
      a:
      b:))
  (defblock (a: v Integer)
    (return v))
  (defblock (b: w Integer)
    (return v)))
