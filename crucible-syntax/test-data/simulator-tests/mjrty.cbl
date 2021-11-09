; This is a slightly larger-scale example.  Here we are proving the
; correctness of the MJRTY algorithm (due to Boyer and Moore) for
; computing the majority value (if it exists) of a sequence of values
; in linear time and constant space.


; Declare the main function of type ()
(defun @main () Unit
  ; `start` defines the entry block to a function with name `start:`
  (start start:
    (print "Hello!\n")

    ; `let` declares immutable variables.  Can be used with fresh symbolic
    ; values, or concrete values
    (let x (fresh Integer))

    ; `funcall` makes a function call
    (let xs (funcall @freshVector 18))
    (let m (funcall @mjrty xs))

    (let precond (funcall @isMajority x xs))

    ; Add assumptions to the verification with `assume!`
    (assume! precond "MJRTY precondition")

    ; Add assertions to the verification with `assert!`
    (assert! (equal? x m) "MJRTY postcondition")

    (let res (funcall @proveObligations))

    (return ())))

; isMajority is a function of type `Integer -> Vector Integer -> Bool`
(defun @isMajority ( (x Integer) (xs (Vector Integer)) ) Bool
  ; Functions can optionally define mutable variables with `registers`
  (registers
    ($i Nat)
    ($n Nat))

  ; Function entry point named `start:`
  (start start:
    (let sz (vector-size xs))
    ; `set-register!` mutates registers
    (set-register! $i 0)
    (set-register! $n 0)
    ; `branch` jumps to a block based on a condition
    (branch (< $i sz) loop: exit:))

  ; Define a block named `loop:`
  (defblock loop:
    ; `if` is an expression.  `branch` is a statement
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
    ; `the` adds a type annotation to an expression.  This statement sets `$xs`
    ; to an empty Vector of Integers
    (set-register! $xs (the (Vector Integer) (vector)))
    (branch (< $i sz) loop: exit:))

  (defblock loop:
    (let x (fresh Integer))
    (set-register! $xs (vector-cons x $xs))
    (set-register! $i (+ $i 1))
    (branch (< $i sz) loop: exit:))

  (defblock exit:
    (return $xs)))

; Hastily written `gethostname` override
(defun @gethostname ( (ptr Pointer) (sz Integer) ) Integer
  (start start:
    (let bytes (fresh Integer))
    (let written (fresh (BitVector bytes)))
    ; if concrete, can use (let written "hostname")
    (assume! (<= bytes sz))
    (pointer-write ptr written)
    (return bytes)))

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
    ; `jump` jumps to another block
    (jump loop-test:)
  )

  (defblock nonzero-k:
    (set-register! $k (if (equal? $x y) (+ $k 1) (- $k 1)))
    (jump loop-test:)
  )

  (defblock loop-exit:
    (return $x))
)
