; This is a slightly larger-scale example.  Here we are proving the
; correctness of the MJRTY algorithm (due to Boyer and Moore) for
; computing the majority value (if it exists) of a sequence of values
; in linear time and constant space.

(defun @main () Unit
  (start start:
    (print "Hello!\n")
    (let x (fresh Integer))
    (let xs (funcall @freshVector 18))
    (let m (funcall @mjrty xs))

    (let precond (funcall @isMajority x xs))
    (assume! precond "MJRTY precondition")
    (assert! (equal? x m) "MJRTY postcondition")

    (let res (funcall @proveObligations))

    (return ())))

(defun @isMajority ( (x Integer) (xs (Vector Integer)) ) Bool
  (registers
    ($i Nat)
    ($n Nat))

  (start start:
    (let sz (vector-size xs))
    (set-register! $i 0)
    (set-register! $n 0)
    (branch (< $i sz) loop: exit:))

  (defblock loop:
    (set-register! $n (+ $n (if (equal? x (vector-get xs $i)) 1 0)))
    (set-register! $i (+ $i 1))
    (branch (< $i sz) loop: exit:))

  (defblock exit:
    (return (< sz (* 2 $n))) ))


(defun @freshVector ((sz Nat)) (Vector Integer)
  (registers
    ($i Nat)
    ($xs (Vector Integer)))

  (start start:
    (set-register! $i 0)
    (set-register! $xs (the (Vector Integer) (vector)))
    (branch (< $i sz) loop: exit:))

  (defblock loop:
    (let x (fresh Integer))
    (set-register! $xs (vector-cons x $xs))
    (set-register! $i (+ $i 1))
    (branch (< $i sz) loop: exit:))

  (defblock exit:
    (return $xs)))


(defun @mjrty ( (xs (Vector Integer)) ) Integer
  (registers
    ($i Nat)
    ($sz Nat)
    ($x Integer)
    ($k Integer))

  (start start:
    (set-register! $sz (vector-size xs))
    (set-register! $i 0)
    (set-register! $k 0)
    (set-register! $x 0)
    (branch (< $i $sz) loop-head: zero-fail:))

  (defblock zero-fail:
    (error "mjrty called on zero-length vector"))

  (defblock loop-test:
    (branch (< $i $sz) loop-head: loop-exit:))

  (defblock loop-head:
    (let y (vector-get xs $i))
    (set-register! $i (+ $i 1))
    (branch (equal? $k 0) zero-k: nonzero-k:)
  )

  (defblock zero-k:
    (set-register! $k 1)
    (set-register! $x y)
    (jump loop-test:)
  )

  (defblock nonzero-k:
    (set-register! $k (if (equal? $x y) (+ $k 1) (- $k 1)))
    (jump loop-test:)
  )

  (defblock loop-exit:
    (return $x))
)