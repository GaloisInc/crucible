
(defun @main () Unit
  (start start:
    (let ba (fresh Bool))
    (assume! ba "assuming")
    (let cba (funcall @concBool ba))
    (println (show cba))

    (let b0 (fresh Bool))
    (branch b0 t: f:))
  (defblock t:
    (let bt (funcall @concBool b0))
    (println (show bt))
    (return ()))
  (defblock f:
    (let bf (funcall @concBool b0))
    (println (show bf))
    (return ())))
