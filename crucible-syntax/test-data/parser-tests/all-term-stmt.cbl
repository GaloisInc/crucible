;; Test all terminating statements other than variants

(defun @test ((b Bool) (m (Maybe Integer))) Any
  (registers
    ($c Bool))
  (start here:
    (set-register! $c b)
    (jump there:))
  (defblock there:
    (let d $c)
    (branch d where: next:))
  (defblock where:
    (let c $c)
    (set-register! $c (not c))
    (jump there:))
  (defblock next:
    (maybe-branch m yep: nope:))
  (defblock (yep: num Integer)
    (let val (to-any num))
    (return val))
  (defblock nope:
    (let msg "nope")
    (error msg))
  (defblock unreachable:
    (let x (the Integer 42))
    (output yep: x)))

(defun @more () Any
  (start here:
    (let test @test)
    (let yep #t)
    (let other (the (Maybe Integer) (just 3)))
    (tail-call test yep other)))
