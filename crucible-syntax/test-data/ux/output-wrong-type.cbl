; Test that output to a label with the wrong parameter type is rejected
(defun @test () Integer
  (start block:
    (let x #t)
    (output dest: x))
  (defblock (dest: y Integer)
    (return y)))
