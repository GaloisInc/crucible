(defun @structs ((x (Struct Bool Integer))) (Struct Unit Nat Bool)
  (start st:
    (let b (get-field 0 x))
    (let i (get-field 1 x))

    (let r1 (struct () (the Nat 5) b))
    (let r2 (set-field r1 1 42))
    (let r3 (set-field r2 2 #f))

    (return r3)
  )
)
