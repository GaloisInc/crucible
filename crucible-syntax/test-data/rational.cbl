(defun @test-rational () Real
  (start start:
    (let v (the Real 0x0f/45))
    (let x (the Real (/ v 2/1)))
    (let r (the Real (+ (mod 1/2 3/2) 22)))
    (let intp (integer? r))
    (return r)))

