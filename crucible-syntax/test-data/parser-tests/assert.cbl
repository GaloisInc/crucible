(defun @test ((n Integer)) Unit
  (registers ($x Bool))
  (start here:
    (let one (the Integer 1))
    (let ok (and (< n one) (< one n)))
    (set-register! $x ok)
    (jump next:))
  (defblock next:
    (let this-x $x)
    (let thing (if this-x #f #t))
    (let more ())
    (assert! (not this-x) "No way, no way at all")
    (return more)))
