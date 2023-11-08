(defun @main () Unit
  (registers
    ($s1 (Sequence Integer))
    ($s2 (Sequence Integer))
  )

  (start start:
    (set-register! $s1 (seq-cons 42 seq-nil))
    (set-register! $s2 seq-nil)

    (let b1 (fresh Bool))
    (let b2 (fresh Bool))
    (let x (fresh Integer))
    (let y (fresh Integer))
    (let z (fresh Integer))
    (let w (fresh Integer))

    (branch b1 l1: l2:))

  (defblock l1:
    (set-register! $s1 (seq-cons x $s1))
    (jump l3:)
  )

  (defblock l2:
    (set-register! $s1 (seq-cons y $s1))
    (jump l3:)
  )

  (defblock l3:
    (branch b2 l4: l5:)
  )


  (defblock l4:
    (set-register! $s2 (seq-cons z $s2))
    (jump l6:)
  )

  (defblock l5:
    (set-register! $s2 (seq-cons w $s2))
    (jump l6:)
  )

  (defblock l6:
    (let s (seq-append $s1 $s2))

    (let _0 (funcall @eqseq s
      (seq-cons (if b1 x y) (seq-cons 42 (seq-cons (if b2 z w) (seq-nil Integer))))))

    (let u1 (from-just (seq-uncons s) "uncons 1"))
    (let v1 (get-field 0 u1))
    (let t1 (get-field 1 u1))

    (let v1alt (from-just (seq-head s) "head 1"))
    (assert! (equal? v1 v1alt) "head 1 eq check")
    (assert! (equal? v1 (if b1 x y)) "head 1 check")

    (let t1alt (from-just (seq-tail s) "tail 1"))
    (let _1 (funcall @eqseq t1 t1alt))
    (let _2 (funcall @eqseq t1 (seq-cons 42 (seq-cons (if b2 z w) (seq-nil Integer)))))

    (let u2 (from-just (seq-uncons t1) "uncons 2"))
    (let v2 (get-field 0 u2))
    (let t2 (get-field 1 u2))

    (let v2alt (from-just (seq-head t1) "head 2"))
    (assert! (equal? v2 v2alt) "head 2 eq check")
    (assert! (equal? v2 42) "head 2 check")

    (let t2alt (from-just (seq-tail t1) "tail 2"))
    (let _3 (funcall @eqseq t2 t2alt))
    (let _4 (funcall @eqseq t2 (seq-cons (if b2 z w) (seq-nil Integer))))

    (return ())
  )
)

(defun @eqseq ( (xs (Sequence Integer)) (ys (Sequence Integer)) ) Unit
  (registers
    ($xs (Sequence Integer))
    ($ys (Sequence Integer)))

  (start st:
    (set-register! $xs xs)
    (set-register! $ys ys)
    (jump loop:))

  (defblock loop:
    (maybe-branch (seq-uncons $xs) xsj: xsn:)
  )

  (defblock (xsj: uxs (Struct Integer (Sequence Integer)))
    (let uys (from-just (seq-uncons $ys) "sequence length mismatch!"))
    (assert! (equal? (get-field 0 uxs) (get-field 0 uys)) "value mismatch!")

    (set-register! $xs (get-field 1 uxs))
    (set-register! $ys (get-field 1 uys))
    (jump loop:)
  )

  (defblock xsn:
    (assert! (seq-nil? $ys) "sequence length mismatch!")
    (return ())
  )
)
