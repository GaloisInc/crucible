(defun @main () Unit
  (registers
    ($s (Sequence Integer))
  )

  (start start:
    (set-register! $s seq-nil)
    (let b (fresh Bool))
    (let x (fresh Integer))
    (let y (fresh Integer))
    (let z (fresh Integer))
    (branch b l1: l2:))

  (defblock l1:
    (set-register! $s (seq-cons x (seq-cons y $s)))
    (jump l3:)
  )

  (defblock l2:
    (set-register! $s (seq-cons z $s))
    (jump l3:)
  )

  (defblock l3:
    (assert! (<= 1 (seq-length $s)) "length test")
    (let u (from-just (seq-uncons $s) "uncons"))

    (let v (if b x z))
    (assert! (equal? v (get-field 0 u)) "head check")
    (assert! (equal? (seq-nil? (get-field 1 u)) (not b)) "tail check")

    (let mu2 (seq-uncons (get-field 1 u)))
    (maybe-branch mu2 j: n:))

  (defblock (j: u2 (Struct Integer (Sequence Integer)))
    (let v2 (get-field 0 u2))
    (let t2 (get-field 1 u2))
    (assert! b "tail 2 condition check")
    (assert! (equal? y v2) "tail 2 value test")
    (assert! (seq-nil? t2) "tail 2 nil test")
    (return ())
  )

  (defblock n:
    (assert! (not b) "tail 2 none check")
    (return ()))
)
