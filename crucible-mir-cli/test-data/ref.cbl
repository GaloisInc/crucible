(defun @main () Unit
  (start start:
    (let r (ref-new (Bitvector 8)))
    (let v-expected (bv 8 42))
    (ref-write (Bitvector 8) r v-expected)
    (let v-actual (ref-read (Bitvector 8) r))
    (assert! (equal? v-expected v-actual) "load of stored value")
    (ref-drop r)

    (return ())))
