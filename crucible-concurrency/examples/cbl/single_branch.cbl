(defun @main () Unit
  (start start:
    (let x (fresh Integer))
    (let p (< 0 x))
    (branch p t: f:))

  (defblock t:
    (jump go:))
  (defblock f:
    (jump go:))

  (defblock go:
    (branch p tt: ff:))

  (defblock tt:
    (output end: ()))
  (defblock ff:
    (output end: ()))

  (defblock (end: z Unit)
    (return ()))
)

(defun @yield () Unit
  (start start:
    (return ())))

(defun @write_effect ((varName (String Unicode))) Unit
  (start start:
    (return ())))

(defun @spawn ((_ (-> Unit Unit))) Unit
  (start start:
    (return ())))
