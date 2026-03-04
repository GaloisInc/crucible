; Test that the error message for maybe-branch on non-Maybe type is reasonable
(defun @test () Integer
  (start block:
    (let x (the Integer 42))
    (maybe-branch x block-just: block-nothing:))
  (defblock (block-just: y Integer)
    (return y))
  (defblock block-nothing:
    (return 0)))
