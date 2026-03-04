; Test that case with wrong number of labels is rejected
(defun @test () Integer
  (start block:
    (let x (the (Variant Integer Bool) (inj 0 (the Integer 1))))
    (case x
      a:))
  (defblock (a: v Integer)
    (return v)))
