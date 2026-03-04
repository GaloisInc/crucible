; Test that the error message for case on non-variant type is reasonable
(defun @test () Integer
  (start block:
    (let x (the Integer 42))
    (case x
      block0:
      block1:))
  (defblock (block0: y Integer)
    (return y))
  (defblock (block1: z Integer)
    (return z)))
